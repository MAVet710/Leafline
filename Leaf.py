import io
import re
import uuid
import json
import hashlib
import sqlite3
from dataclasses import dataclass
from datetime import datetime, date, timezone
from typing import Dict, List, Tuple, Optional

import streamlit as st
import pdfplumber
import fitz  # PyMuPDF (requires Python 3.11/3.12; will fail on 3.13 in many envs)
from PIL import Image
import pytesseract
from dateutil import parser as dateparser

from reportlab.lib.pagesizes import letter
from reportlab.lib.units import inch
from reportlab.lib.utils import ImageReader
from reportlab.pdfgen import canvas


# ============================
# LITIGATION-GRADE CONFIG
# ============================

APP_NAME = "Leafline"
APP_VERSION = "1.0.0-litigation"
DB_PATH = "leafline_audit.db"

STATE_OPTIONS = ["MA", "NY", "NJ"]
PRODUCT_TYPES = ["Flower", "Pre-roll", "Concentrate", "Vape", "Edible", "Topical", "Tincture"]

# STARTER required panels structure — replace/expand with client’s vetted requirements
REQUIRED_PANELS: Dict[str, Dict[str, List[str]]] = {
    "MA": {
        "Flower": ["Cannabinoids", "Microbials", "Mycotoxins", "Pesticides", "Heavy Metals", "Moisture", "Water Activity", "Foreign Matter"],
        "Pre-roll": ["Cannabinoids", "Microbials", "Mycotoxins", "Pesticides", "Heavy Metals", "Moisture", "Water Activity", "Foreign Matter"],
        "Concentrate": ["Cannabinoids", "Residual Solvents", "Microbials", "Mycotoxins", "Pesticides", "Heavy Metals"],
        "Vape": ["Cannabinoids", "Residual Solvents", "Heavy Metals", "Microbials"],
        "Edible": ["Cannabinoids", "Microbials", "Mycotoxins", "Heavy Metals", "Pesticides"],
        "Topical": ["Cannabinoids", "Microbials", "Heavy Metals"],
        "Tincture": ["Cannabinoids", "Microbials", "Heavy Metals"],
    },
    "NY": {
        "Flower": ["Cannabinoids", "Terpenes", "Microbials", "Mycotoxins", "Pesticides", "Heavy Metals", "Moisture", "Water Activity", "Foreign Matter"],
        "Pre-roll": ["Cannabinoids", "Terpenes", "Microbials", "Mycotoxins", "Pesticides", "Heavy Metals", "Moisture", "Water Activity", "Foreign Matter"],
        "Concentrate": ["Cannabinoids", "Terpenes", "Residual Solvents", "Microbials", "Mycotoxins", "Pesticides", "Heavy Metals"],
        "Vape": ["Cannabinoids", "Terpenes", "Residual Solvents", "Heavy Metals", "Microbials"],
        "Edible": ["Cannabinoids", "Microbials", "Mycotoxins", "Heavy Metals", "Pesticides"],
        "Topical": ["Cannabinoids", "Microbials", "Heavy Metals"],
        "Tincture": ["Cannabinoids", "Microbials", "Heavy Metals"],
    },
    "NJ": {
        "Flower": ["Cannabinoids", "Microbials", "Mycotoxins", "Pesticides", "Heavy Metals", "Moisture", "Water Activity", "Foreign Matter"],
        "Pre-roll": ["Cannabinoids", "Microbials", "Mycotoxins", "Pesticides", "Heavy Metals", "Moisture", "Water Activity", "Foreign Matter"],
        "Concentrate": ["Cannabinoids", "Residual Solvents", "Microbials", "Mycotoxins", "Pesticides", "Heavy Metals"],
        "Vape": ["Cannabinoids", "Residual Solvents", "Heavy Metals", "Microbials"],
        "Edible": ["Cannabinoids", "Microbials", "Mycotoxins", "Heavy Metals"],
        "Topical": ["Cannabinoids", "Microbials", "Heavy Metals"],
        "Tincture": ["Cannabinoids", "Microbials", "Heavy Metals"],
    },
}

# Option 2: Terpenes should be CHECKED + REPORTED as optional for MA and NJ
OPTIONAL_PANELS_BY_STATE: Dict[str, List[str]] = {
    "MA": ["Terpenes"],
    "NJ": ["Terpenes"],
    "NY": [],  # NY already treats terpenes as required in REQUIRED_PANELS above
}

# Panel detection keywords (not “the rules”, just detection)
PANEL_KEYWORDS = {
    "Cannabinoids": [r"\bcannabinoid", r"\bpotency", r"\bTHC\b", r"\bCBD\b", r"Total\s+THC", r"Total\s+CBD"],
    "Terpenes": [r"\bterpene", r"\bterpenoid", r"\blimonene\b", r"\bmyrcene\b", r"\bcaryophyllene\b", r"\bpinene\b", r"\blinalool\b"],
    "Moisture": [r"\bmoisture\b"],
    "Water Activity": [r"\bwater\s*activity\b", r"\baw\b"],
    "Microbials": [r"\bmicrobial", r"\bE\.\s*coli\b", r"\bsalmonella\b", r"\byeast\b", r"\bmold\b", r"\bTYMC\b"],
    "Mycotoxins": [r"\bmycotoxin", r"\baflatoxin\b", r"\bochratoxin\b"],
    "Pesticides": [r"\bpesticide", r"\bpyrethrin", r"\bmyclobutanil\b"],
    "Heavy Metals": [r"\bheavy\s*metals?\b", r"\blead\b", r"\barsenic\b", r"\bcadmium\b", r"\bmercury\b"],
    "Residual Solvents": [r"\bsolvent", r"\bresidual\s*solvent", r"\bbutane\b", r"\bpropane\b", r"\bethanol\b"],
    "Foreign Matter": [r"\bforeign\s*matter\b"],
}

FIELD_PATTERNS = {
    "lab_name": [r"Lab\s*Name[:\s]+(.+)", r"Certificate\s+of\s+Analysis.*?\n(.+Labs?.*)"],
    "sample_id": [r"Sample\s*ID[:\s]+([A-Za-z0-9\-_]+)", r"Sample\s*:\s*([A-Za-z0-9\-_]+)"],
    "batch_id": [r"Batch\s*(?:#|No\.|Number)?[:\s]+([A-Za-z0-9\-_]+)", r"Lot\s*(?:#|No\.)?[:\s]+([A-Za-z0-9\-_]+)"],
    "matrix": [r"Matrix[:\s]+(.+)", r"Category[:\s]+(.+)", r"Sample\s*Type[:\s]+(.+)"],
    "completed_date": [r"(?:Completed|Reported|Finalized)\s*[:\s]+([0-9]{1,2}[/\-][0-9]{1,2}[/\-][0-9]{2,4})"],
    "received_date": [r"Received\s*[:\s]+([0-9]{1,2}[/\-][0-9]{1,2}[/\-][0-9]{2,4})"],
    "collected_date": [r"Collected\s*[:\s]+([0-9]{1,2}[/\-][0-9]{1,2}[/\-][0-9]{2,4})"],
    "total_thc": [r"Total\s*THC[:\s]+([0-9]+(?:\.[0-9]+)?)\s*%"],
    "total_cbd": [r"Total\s*CBD[:\s]+([0-9]+(?:\.[0-9]+)?)\s*%"],
    "total_cannabinoids": [r"Total\s*Cannabinoids[:\s]+([0-9]+(?:\.[0-9]+)?)\s*%"],
    "moisture": [r"Moisture[:\s]+([0-9]+(?:\.[0-9]+)?)\s*%"],
    "water_activity": [r"Water\s*Activity[:\s]+([0-9]+(?:\.[0-9]+)?)\s*(?:aw)?"],
}

RD_QA_PATTERNS = [
    r"\bR&D\b",
    r"\bResearch\b",
    r"\bfor\s+research\s+only\b",
    r"\bQA\b\s*testing\b",
]


# ============================
# AUDIT LOG (SQLite)
# ============================

def init_db():
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute("""
    CREATE TABLE IF NOT EXISTS records (
        record_id TEXT PRIMARY KEY,
        created_at_utc TEXT NOT NULL,
        uploader TEXT,
        source_filename TEXT NOT NULL,
        source_sha256 TEXT NOT NULL,
        source_size_bytes INTEGER NOT NULL,
        state TEXT NOT NULL,
        product_type TEXT NOT NULL,
        ruleset_version TEXT NOT NULL,
        parsing_method TEXT NOT NULL,
        ocr_confidence REAL,
        notes TEXT
    )
    """)
    cur.execute("""
    CREATE TABLE IF NOT EXISTS events (
        event_id TEXT PRIMARY KEY,
        record_id TEXT NOT NULL,
        event_type TEXT NOT NULL,
        event_at_utc TEXT NOT NULL,
        event_payload TEXT,
        FOREIGN KEY(record_id) REFERENCES records(record_id)
    )
    """)
    conn.commit()
    conn.close()

def utc_now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")

def db_insert_record(row: dict):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute("""
    INSERT INTO records (
        record_id, created_at_utc, uploader, source_filename, source_sha256, source_size_bytes,
        state, product_type, ruleset_version, parsing_method, ocr_confidence, notes
    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    """, (
        row["record_id"], row["created_at_utc"], row.get("uploader"),
        row["source_filename"], row["source_sha256"], row["source_size_bytes"],
        row["state"], row["product_type"], row["ruleset_version"],
        row["parsing_method"], row.get("ocr_confidence"), row.get("notes")
    ))
    conn.commit()
    conn.close()

def db_insert_event(record_id: str, event_type: str, payload: dict):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute("""
    INSERT INTO events (event_id, record_id, event_type, event_at_utc, event_payload)
    VALUES (?, ?, ?, ?, ?)
    """, (
        str(uuid.uuid4()),
        record_id,
        event_type,
        utc_now_iso(),
        json.dumps(payload, ensure_ascii=False),
    ))
    conn.commit()
    conn.close()


# ============================
# UTILITIES
# ============================

@dataclass
class Evidence:
    page_index: Optional[int]  # 0-based
    snippet: str

@dataclass
class Finding:
    severity: str  # HOLD, WARN, INFO
    rule_id: str
    title: str
    evidence: Evidence
    recommendation: str

def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

def safe_parse_date(s: str) -> Optional[date]:
    try:
        d = dateparser.parse(s, dayfirst=False, yearfirst=False)
        return d.date() if d else None
    except Exception:
        return None

def extract_text_from_pdf(pdf_bytes: bytes) -> Tuple[str, List[str]]:
    per_page = []
    with pdfplumber.open(io.BytesIO(pdf_bytes)) as pdf:
        for p in pdf.pages:
            per_page.append(p.extract_text() or "")
    return "\n\n".join(per_page), per_page

def render_pdf_page_image(pdf_bytes: bytes, page_index: int, zoom: float = 2.0) -> Image.Image:
    doc = fitz.open(stream=pdf_bytes, filetype="pdf")
    page = doc.load_page(page_index)
    mat = fitz.Matrix(zoom, zoom)
    pix = page.get_pixmap(matrix=mat, alpha=False)
    return Image.open(io.BytesIO(pix.tobytes("png")))

def ocr_image_with_conf(img: Image.Image) -> Tuple[str, Optional[float]]:
    """
    Returns OCR text + average confidence (0-100), or None if not available.
    """
    try:
        data = pytesseract.image_to_data(img, output_type=pytesseract.Output.DICT)
        confs = []
        for c in data.get("conf", []):
            try:
                ci = float(c)
                if ci >= 0:
                    confs.append(ci)
            except Exception:
                continue
        avg_conf = sum(confs) / len(confs) if confs else None
        text = pytesseract.image_to_string(img)
        return text, avg_conf
    except Exception:
        return "", None

def ocr_pdf_pages(pdf_bytes: bytes) -> Tuple[str, List[str], Optional[float], bool]:
    """
    OCR every page. Returns (full_text, per_page_text, avg_conf, ok)
    """
    try:
        doc = fitz.open(stream=pdf_bytes, filetype="pdf")
        per_page = []
        confs = []
        for i in range(doc.page_count):
            img = render_pdf_page_image(pdf_bytes, i, zoom=2.0)
            txt, conf = ocr_image_with_conf(img)
            per_page.append(txt)
            if conf is not None:
                confs.append(conf)
        full_text = "\n\n".join(per_page)
        avg_conf = sum(confs) / len(confs) if confs else None
        return full_text, per_page, avg_conf, True
    except Exception:
        return "", [], None, False

def extract_fields(text: str) -> Dict[str, str]:
    out: Dict[str, str] = {}
    for field, patterns in FIELD_PATTERNS.items():
        for pat in patterns:
            m = re.search(pat, text, flags=re.IGNORECASE | re.MULTILINE)
            if m:
                out[field] = m.group(1).strip()
                break
    return out

def detect_panels(text: str) -> Dict[str, bool]:
    detected = {}
    for panel, pats in PANEL_KEYWORDS.items():
        detected[panel] = any(re.search(p, text, flags=re.IGNORECASE) for p in pats)
    return detected

def find_first_match(per_page_text: List[str], patterns: List[str], max_snip: int = 220) -> Evidence:
    for i, t in enumerate(per_page_text):
        for pat in patterns:
            m = re.search(pat, t, flags=re.IGNORECASE)
            if m:
                start = max(m.start() - 80, 0)
                end = min(m.end() + 120, len(t))
                snippet = t[start:end].strip().replace("\n", " ")
                if len(snippet) > max_snip:
                    snippet = snippet[:max_snip].rstrip() + "…"
                return Evidence(page_index=i, snippet=snippet)
    return Evidence(page_index=None, snippet="Not detected in extracted text.")

def overall_status(findings: List[Finding]) -> str:
    sevs = [f.severity for f in findings]
    if "HOLD" in sevs:
        return "HOLD"
    if "WARN" in sevs:
        return "NEEDS REVIEW"
    return "PASS"


# ============================
# RULE ENGINE (LITIGATION SAFE)
# ============================

def build_findings(
    state: str,
    product_type: str,
    fields: Dict[str, str],
    panels_detected: Dict[str, bool],
    per_page_text: List[str],
    freshness_days: int,
) -> List[Finding]:
    findings: List[Finding] = []

    required = REQUIRED_PANELS.get(state, {}).get(product_type, [])
    missing = [p for p in required if not panels_detected.get(p, False)]

    # HOLD: missing required panels (evidence is "not detected")
    for idx, p in enumerate(missing, start=1):
        findings.append(
            Finding(
                severity="HOLD",
                rule_id=f"{state}-MISS-PANEL-{idx:03d}",
                title=f"Required panel missing: {p}",
                evidence=Evidence(page_index=None, snippet=f"Panel '{p}' not detected in extracted document text."),
                recommendation="Request an updated COA including this panel, results, units, and testing method.",
            )
        )

    # WARN: R&D/QA language
    ev_rd = find_first_match(per_page_text, RD_QA_PATTERNS)
    if ev_rd.page_index is not None:
        findings.append(
            Finding(
                severity="WARN",
                rule_id=f"{state}-DOC-TYPE-001",
                title="Document appears R&D/QA oriented (not clearly a regulatory compliance COA)",
                evidence=ev_rd,
                recommendation="Confirm whether a regulatory compliance COA is required for this matter; request compliance-form COA if needed.",
            )
        )

    # WARN: COA freshness if date extracted
    completed_raw = fields.get("completed_date", "")
    completed_dt = safe_parse_date(completed_raw) if completed_raw else None
    if completed_raw and completed_dt and freshness_days > 0:
        age = (date.today() - completed_dt).days
        if age > freshness_days:
            ev_date = find_first_match(per_page_text, [re.escape(completed_raw)])
            findings.append(
                Finding(
                    severity="WARN",
                    rule_id=f"{state}-FRESH-001",
                    title="COA may be outdated per configured freshness threshold",
                    evidence=Evidence(
                        page_index=ev_date.page_index,
                        snippet=f"Completed/Reported date: {completed_raw} (~{age} days old). Threshold: {freshness_days} days.",
                    ),
                    recommendation="Request a more recent COA or document why this COA is acceptable for the intended purpose.",
                )
            )
    elif freshness_days > 0:
        findings.append(
            Finding(
                severity="INFO",
                rule_id=f"{state}-FRESH-INFO-001",
                title="Completed/Reported date not detected (freshness check limited)",
                evidence=Evidence(page_index=None, snippet="No completed/reported date was reliably extracted."),
                recommendation="Verify completed/reported date manually; consider adding lab-specific extraction patterns.",
            )
        )

    # INFO: extracted potency fields (if present)
    if fields.get("total_thc"):
        ev = find_first_match(per_page_text, [r"Total\s*THC", re.escape(fields["total_thc"])])
        findings.append(
            Finding(
                severity="INFO",
                rule_id=f"{state}-POT-INFO-001",
                title="Total THC extracted",
                evidence=Evidence(page_index=ev.page_index, snippet=f"Total THC: {fields['total_thc']}%"),
                recommendation="None.",
            )
        )

    # ==========
    # OPTION 2: Terpenes always reported as INFO for MA/NJ (optional)
    # ==========
    if "Terpenes" in OPTIONAL_PANELS_BY_STATE.get(state, []):
        if panels_detected.get("Terpenes"):
            ev = find_first_match(per_page_text, PANEL_KEYWORDS["Terpenes"])
            findings.append(
                Finding(
                    severity="INFO",
                    rule_id=f"{state}-TERP-INFO-001",
                    title="Terpenes panel detected (optional)",
                    evidence=ev,
                    recommendation="None.",
                )
            )
        else:
            findings.append(
                Finding(
                    severity="INFO",
                    rule_id=f"{state}-TERP-INFO-002",
                    title="Terpenes panel not detected (optional)",
                    evidence=Evidence(page_index=None, snippet="No terpene panel keywords were detected in extracted text."),
                    recommendation="None (terpenes are optional for this report).",
                )
            )

    return findings


# ============================
# PDF REPORT (LITIGATION)
# ============================

def wrap_text(c: canvas.Canvas, text: str, x: float, y: float, max_width: float, font="Helvetica", size=10, leading=12) -> float:
    c.setFont(font, size)
    words = (text or "").split()
    line = ""
    for w in words:
        test = (line + " " + w).strip()
        if c.stringWidth(test, font, size) <= max_width:
            line = test
        else:
            c.drawString(x, y, line)
            y -= leading
            line = w
    if line:
        c.drawString(x, y, line)
        y -= leading
    return y

def generate_pdf_report(
    *,
    record_id: str,
    state: str,
    product_type: str,
    ruleset_version: str,
    uploader: str,
    source_filename: str,
    source_sha256: str,
    source_size_bytes: int,
    parsing_method: str,
    ocr_confidence: Optional[float],
    fields: Dict[str, str],
    panels_detected: Dict[str, bool],
    findings: List[Finding],
    source_file_bytes: bytes,
) -> bytes:
    buf = io.BytesIO()
    c = canvas.Canvas(buf, pagesize=letter)
    width, height = letter
    margin = 0.75 * inch
    x = margin
    y = height - margin

    generated_utc = utc_now_iso()
    status = overall_status(findings)

    # ---- Page 1: Executive Summary ----
    c.setFont("Helvetica-Bold", 16)
    c.drawString(x, y, f"{APP_NAME} — COA Review & Compliance Findings")
    y -= 18

    c.setFont("Helvetica", 10)
    c.drawString(x, y, f"Record ID: {record_id}")
    y -= 12
    c.drawString(x, y, f"Generated (UTC): {generated_utc}")
    y -= 12
    c.drawString(x, y, f"Uploader: {uploader or 'Not provided'}")
    y -= 12
    c.drawString(x, y, f"Jurisdiction Applied: {state} | Product Type: {product_type}")
    y -= 12
    c.drawString(x, y, f"Ruleset Version: {ruleset_version}")
    y -= 12
    c.drawString(x, y, f"App Version: {APP_VERSION}")
    y -= 12
    c.drawString(
        x,
        y,
        f"Parsing Method: {parsing_method} | OCR Confidence: {('N/A' if ocr_confidence is None else f'{ocr_confidence:.1f}/100')}",
    )
    y -= 14

    c.setFont("Helvetica-Bold", 14)
    c.drawString(x, y, f"Overall Status: {status}")
    y -= 18

    c.setFont("Helvetica-Bold", 12)
    c.drawString(x, y, "Document & Sample Identity (as extracted)")
    y -= 14

    c.setFont("Helvetica", 10)
    identity = [
        ("Source File", source_filename),
        ("Source SHA-256", source_sha256),
        ("File Size (bytes)", str(source_size_bytes)),
        ("Lab", fields.get("lab_name", "Not detected")),
        ("Sample ID", fields.get("sample_id", "Not detected")),
        ("Batch/Lot", fields.get("batch_id", "Not detected")),
        ("Matrix/Category", fields.get("matrix", "Not detected")),
        ("Collected", fields.get("collected_date", "Not detected")),
        ("Received", fields.get("received_date", "Not detected")),
        ("Completed/Reported", fields.get("completed_date", "Not detected")),
        ("Terpenes Panel Detected", "Yes" if panels_detected.get("Terpenes") else "No"),
    ]
    for k, v in identity:
        y = wrap_text(c, f"{k}: {v}", x, y, width - 2 * margin)
        if y < margin + 90:
            c.showPage()
            y = height - margin

    y -= 6
    c.setFont("Helvetica-Bold", 12)
    c.drawString(x, y, "Panels (Required vs Detected)")
    y -= 14

    required = REQUIRED_PANELS.get(state, {}).get(product_type, [])
    c.setFont("Helvetica", 10)
    for p in required:
        detected = "Yes" if panels_detected.get(p, False) else "No"
        c.drawString(x, y, f"- {p}: Detected = {detected} | Required = Yes")
        y -= 12
        if y < margin + 70:
            c.showPage()
            y = height - margin

    # Optional panels section (Option 2)
    optional_panels = OPTIONAL_PANELS_BY_STATE.get(state, [])
    if optional_panels:
        y -= 6
        c.setFont("Helvetica-Bold", 12)
        c.drawString(x, y, "Optional Panels (Checked for Reporting)")
        y -= 14
        c.setFont("Helvetica", 10)
        for p in optional_panels:
            detected = "Yes" if panels_detected.get(p, False) else "No"
            c.drawString(x, y, f"- {p}: Detected = {detected} | Required = No (optional)")
            y -= 12
            if y < margin + 70:
                c.showPage()
                y = height - margin

    # ---- Page 2: Findings ----
    c.showPage()
    y = height - margin

    c.setFont("Helvetica-Bold", 14)
    c.drawString(x, y, "Findings")
    y -= 18

    def print_findings(sev: str, y: float) -> float:
        items = [f for f in findings if f.severity == sev]
        if not items:
            return y
        c.setFont("Helvetica-Bold", 12)
        c.drawString(x, y, sev)
        y -= 14
        for fnd in items:
            c.setFont("Helvetica-Bold", 10)
            c.drawString(x, y, f"{fnd.rule_id} — {fnd.title}")
            y -= 12

            pg = "N/A" if fnd.evidence.page_index is None else str(fnd.evidence.page_index + 1)
            y = wrap_text(c, f"Evidence (page {pg}): {fnd.evidence.snippet}", x + 12, y, width - 2 * margin - 12)
            y = wrap_text(c, f"Recommended Action: {fnd.recommendation}", x + 12, y, width - 2 * margin - 12)
            y -= 6
            if y < margin + 70:
                c.showPage()
                y = height - margin
        y -= 10
        return y

    y = print_findings("HOLD", y)
    y = print_findings("WARN", y)
    y = print_findings("INFO", y)

    # ---- Page 3+: Evidence Appendix (PDF page images) ----
    # Embed referenced page images only if we have a PDF (source_file_bytes contains PDF bytes)
    appendix_items = [f for f in findings if f.evidence.page_index is not None]
    if appendix_items and source_file_bytes:
        c.showPage()
        y = height - margin
        c.setFont("Helvetica-Bold", 14)
        c.drawString(x, y, "Evidence Appendix (Document Page Images)")
        y -= 18
        c.setFont("Helvetica", 10)
        y = wrap_text(
            c,
            "For each finding with a located page reference, the corresponding document page image is embedded below. "
            "If OCR was used, the image reflects the source rendering used for OCR; text location may not be exact.",
            x,
            y,
            width - 2 * margin,
        )

        for fnd in appendix_items:
            pg = fnd.evidence.page_index
            c.showPage()
            y = height - margin
            c.setFont("Helvetica-Bold", 12)
            c.drawString(x, y, f"{fnd.rule_id} — {fnd.title}")
            y -= 14
            c.setFont("Helvetica", 10)
            c.drawString(x, y, f"Referenced page: {pg + 1}")
            y -= 12
            y = wrap_text(c, f"Snippet: {fnd.evidence.snippet}", x, y, width - 2 * margin)
            y -= 8

            try:
                page_img = render_pdf_page_image(source_file_bytes, pg, zoom=2.0)
                max_w = width - 2 * margin
                max_h = height - 2 * margin - 80
                iw, ih = page_img.size
                scale = min(max_w / iw, max_h / ih)
                dw, dh = iw * scale, ih * scale
                img_x = x
                img_y = margin
                c.drawImage(ImageReader(page_img), img_x, img_y, width=dw, height=dh, preserveAspectRatio=True, mask="auto")
            except Exception:
                c.drawString(x, y, "Unable to embed page image (rendering error).")

    # ---- Final page: Methods & Limitations ----
    c.showPage()
    y = height - margin
    c.setFont("Helvetica-Bold", 14)
    c.drawString(x, y, "Methods & Limitations")
    y -= 18
    c.setFont("Helvetica", 10)
    method_text = (
        f"{APP_NAME} performed document parsing and rule-based checks using the jurisdiction selected by the user. "
        "Findings reflect what was detected in the provided document at the time of report generation. "
        "This report does not validate laboratory truthfulness, sampling integrity, chain-of-custody outside of this application, "
        "or the authenticity of the underlying results beyond the document provided. "
        "If OCR was used, extracted text may contain errors; OCR confidence is provided where available. "
        "A 'missing panel' finding means the panel was not detected in extracted text and may require human verification against the original document image."
    )
    y = wrap_text(c, method_text, x, y, width - 2 * margin)

    y -= 10
    c.setFont("Helvetica-Bold", 11)
    c.drawString(x, y, "Reproducibility Metadata")
    y -= 14
    c.setFont("Helvetica", 10)
    meta_lines = [
        f"Record ID: {record_id}",
        f"Generated (UTC): {generated_utc}",
        f"Source SHA-256: {source_sha256}",
        f"Ruleset Version: {ruleset_version}",
        f"App Version: {APP_VERSION}",
        f"Parsing Method: {parsing_method}",
        f"OCR Confidence: {('N/A' if ocr_confidence is None else f'{ocr_confidence:.1f}/100')}",
    ]
    for line in meta_lines:
        y = wrap_text(c, line, x, y, width - 2 * margin)

    c.save()
    return buf.getvalue()


# ============================
# STREAMLIT UI
# ============================

st.set_page_config(page_title="Leafline — Litigation COA Analyzer", layout="wide")
init_db()

st.title("Leafline — COA Analysis (Litigation Mode)")
st.caption("Uploads are hashed and logged. Reports are versioned and include evidence references.")

# Optional: simple access gate using Streamlit secrets
# Add in Streamlit secrets:
# LEAFLINE_PASSWORD="yourpassword"
if "LEAFLINE_PASSWORD" in st.secrets:
    pw = st.text_input("Access password", type="password")
    if pw != st.secrets["LEAFLINE_PASSWORD"]:
        st.stop()

col1, col2, col3 = st.columns([1, 1, 1])
with col1:
    state = st.selectbox("Jurisdiction", STATE_OPTIONS, index=0)
with col2:
    product_type = st.selectbox("Product type", PRODUCT_TYPES, index=0)
with col3:
    freshness_days = st.number_input("COA freshness threshold (days)", min_value=0, max_value=3650, value=365, step=30)

uploader = st.text_input("Uploader / reviewer identifier (optional)", value="")

uploaded = st.file_uploader("Upload COA (PDF, PNG, JPG)", type=["pdf", "png", "jpg", "jpeg"])

if uploaded:
    file_bytes = uploaded.read()
    source_sha = sha256_bytes(file_bytes)
    record_id = str(uuid.uuid4())
    ruleset_version = f"{state}_v1.0_{datetime.now().strftime('%Y-%m-%d')}"
    created_at = utc_now_iso()
    source_size = len(file_bytes)

    st.write(f"**Record ID:** `{record_id}`")
    st.write(f"**Source SHA-256:** `{source_sha}`")

    # Extract text + determine parsing method
    is_pdf = uploaded.name.lower().endswith(".pdf")
    parsing_method = ""
    ocr_conf = None

    extracted_text = ""
    per_page_text: List[str] = []

    with st.spinner("Extracting text..."):
        if is_pdf:
            extracted_text, per_page_text = extract_text_from_pdf(file_bytes)
            # If very low text, attempt OCR
            if len(re.sub(r"\s+", "", extracted_text)) < 500:
                ocr_text, ocr_pages, avg_conf, ok = ocr_pdf_pages(file_bytes)
                if ok and len(re.sub(r"\s+", "", ocr_text)) > len(re.sub(r"\s+", "", extracted_text)):
                    extracted_text = ocr_text
                    per_page_text = ocr_pages
                    parsing_method = "OCR(PDF pages)"
                    ocr_conf = avg_conf
                else:
                    parsing_method = "PDF text extraction (OCR unavailable/insufficient)"
            else:
                parsing_method = "PDF text extraction"
        else:
            try:
                img = Image.open(io.BytesIO(file_bytes))
                txt, conf = ocr_image_with_conf(img)
                extracted_text = txt
                per_page_text = [txt]
                parsing_method = "OCR(Image)"
                ocr_conf = conf
            except Exception:
                parsing_method = "Image OCR failed"
                extracted_text = ""
                per_page_text = []

    # Store record + audit events
    db_insert_record({
        "record_id": record_id,
        "created_at_utc": created_at,
        "uploader": uploader or None,
        "source_filename": uploaded.name,
        "source_sha256": source_sha,
        "source_size_bytes": source_size,
        "state": state,
        "product_type": product_type,
        "ruleset_version": ruleset_version,
        "parsing_method": parsing_method,
        "ocr_confidence": ocr_conf,
        "notes": None,
    })
    db_insert_event(record_id, "UPLOAD_INGESTED", {
        "filename": uploaded.name,
        "sha256": source_sha,
        "size_bytes": source_size,
        "state": state,
        "product_type": product_type,
        "ruleset_version": ruleset_version,
        "parsing_method": parsing_method,
        "ocr_confidence": ocr_conf,
        "app_version": APP_VERSION,
    })

    if parsing_method.startswith("OCR"):
        st.info(f"OCR used. Confidence: {('N/A' if ocr_conf is None else f'{ocr_conf:.1f}/100')}")
    else:
        st.success("Text-based PDF extraction used (OCR not required).")

    with st.expander("Extracted text (debug)"):
        st.text(extracted_text[:25000] if extracted_text else "No text extracted.")

    fields = extract_fields(extracted_text)
    panels_detected = detect_panels(extracted_text)
    findings = build_findings(
        state=state,
        product_type=product_type,
        fields=fields,
        panels_detected=panels_detected,
        per_page_text=per_page_text,
        freshness_days=int(freshness_days),
    )

    st.subheader("Preview")
    st.write(f"**Overall Status:** {overall_status(findings)}")
    st.json({
        "fields": fields,
        "panels_detected": panels_detected,
        "parsing_method": parsing_method,
        "ocr_confidence": ocr_conf,
        "ruleset_version": ruleset_version,
        "app_version": APP_VERSION,
    })

    # Generate PDF report
    pdf_bytes = generate_pdf_report(
        record_id=record_id,
        state=state,
        product_type=product_type,
        ruleset_version=ruleset_version,
        uploader=uploader,
        source_filename=uploaded.name,
        source_sha256=source_sha,
        source_size_bytes=source_size,
        parsing_method=parsing_method,
        ocr_confidence=ocr_conf,
        fields=fields,
        panels_detected=panels_detected,
        findings=findings,
        source_file_bytes=file_bytes if is_pdf else b"",  # page images only for PDFs in this MVP
    )

    report_sha = sha256_bytes(pdf_bytes)
    db_insert_event(record_id, "REPORT_GENERATED", {
        "report_sha256": report_sha,
        "overall_status": overall_status(findings),
        "finding_count": len(findings),
        "ruleset_version": ruleset_version,
        "app_version": APP_VERSION,
    })

    st.write(f"**Report SHA-256:** `{report_sha}`")

    st.download_button(
        label="Download Litigation PDF Report",
        data=pdf_bytes,
        file_name=f"Leafline_Report_{state}_{product_type}_{record_id}.pdf",
        mime="application/pdf",
    )

    st.caption("Note: Download events are not reliably detectable in Streamlit; report generation is logged with hash.")
else:
    st.info("Upload a COA to generate a litigation-grade PDF report.")
