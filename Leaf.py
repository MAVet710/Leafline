"""
Leafline — COA Analyzer
Full single-file Streamlit app with:
- PDF + image ingestion
- Text extraction + OCR fallback
- State selector (MA/NY/NJ) + product type selector
- Panel detection + required/optional checks (Option 2: Terpenes optional for MA/NJ; required for NY)
- ND/NT handling (ND treated as favorable; NT treated as "not tested")
- Dominant cannabinoids + dominant terpenes (top 3)
- Oil-product rule: warn when Δ8 is high while Δ9 is also present
- On-screen summary BEFORE export
- Improved PDF export: plain-language, scannable sections + tables + glossary + evidence appendix
- Audit trail (SQLite) with hashes
"""

import io
import re
import uuid
import json
import hashlib
import sqlite3
from dataclasses import dataclass
from datetime import datetime, date, timezone
from typing import Dict, List, Tuple, Optional, Any

import streamlit as st
import pdfplumber
import fitz  # PyMuPDF (best with Python 3.11/3.12)
from PIL import Image
import pytesseract
from dateutil import parser as dateparser

from reportlab.lib.pagesizes import letter
from reportlab.lib.units import inch
from reportlab.lib.utils import ImageReader
from reportlab.pdfgen import canvas


# ============================
# CONFIG
# ============================

APP_NAME = "Leafline"
APP_VERSION = "1.1.0"
DB_PATH = "leafline_audit.db"

STATE_OPTIONS = ["MA", "NY", "NJ"]
PRODUCT_TYPES = ["Flower", "Pre-roll", "Concentrate", "Vape", "Edible", "Topical", "Tincture"]
OIL_PRODUCT_TYPES = {"Concentrate", "Vape", "Tincture"}  # “oil” types for Δ8/Δ9 check


# ============================
# STATE RULE PACKS (STARTER)
# ============================

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

# Option 2: Terpenes checked + reported as OPTIONAL for MA and NJ (NY requires)
OPTIONAL_PANELS_BY_STATE: Dict[str, List[str]] = {
    "MA": ["Terpenes"],
    "NJ": ["Terpenes"],
    "NY": [],
}

# ============================
# PANEL + FIELD DETECTION
# ============================

PANEL_KEYWORDS = {
    "Cannabinoids": [r"\bcannabinoid", r"\bpotency", r"\bTHC\b", r"\bCBD\b", r"Total\s+THC", r"Total\s+CBD"],
    "Terpenes": [
        r"\bterpene", r"\bterpenoid", r"\blimonene\b", r"\bmyrcene\b", r"\bcaryophyllene\b", r"\bpinene\b",
        r"\blinalool\b", r"Terpenes\s+Date\s+Completed"
    ],
    "Moisture": [r"\bmoisture\b"],
    "Water Activity": [r"\bwater\s*activity\b", r"\baw\b", r"\bA[wW]\b"],
    "Microbials": [r"\bmicrobial", r"\bE\.\s*coli\b", r"\bsalmonella\b", r"\byeast\b", r"\bmold\b", r"\bTYMC\b"],
    "Mycotoxins": [r"\bmycotoxin", r"\baflatoxin\b", r"\bochratoxin\b"],
    "Pesticides": [r"\bpesticide", r"\bpyrethrin", r"\bmyclobutanil\b"],
    "Heavy Metals": [r"\bheavy\s*metals?\b", r"\blead\b", r"\barsenic\b", r"\bcadmium\b", r"\bmercury\b"],
    "Residual Solvents": [r"\bsolvent", r"\bresidual\s*solvent", r"\bbutane\b", r"\bpropane\b", r"\bethanol\b"],
    "Foreign Matter": [r"\bforeign\s*matter\b", r"\bforeign\s*material\b", r"\bvisual\s*inspection\b", r"\bfilth\b"],
}

FIELD_PATTERNS = {
    "lab_name": [r"Lab\s*Name[:\s]+(.+)", r"Certificate\s+of\s+Analysis.*?\n(.+Labs?.*)"],
    "sample_id": [r"Sample\s*(?:#|ID)[:\s]+([A-Za-z0-9\-_]+)", r"Sample\s*:\s*([A-Za-z0-9\-_]+)"],
    "batch_id": [r"Batch\s*(?:#|No\.|Number|ID)?[:\s]+([A-Za-z0-9\-_]+)", r"Lot\s*(?:#|No\.)?[:\s]+([A-Za-z0-9\-_]+)"],
    "matrix": [r"Matrix[:\s]+(.+)", r"Category[:\s]+(.+)", r"Sample\s*Type[:\s]+(.+)", r"Product\s*Type[:\s]+(.+)"],
    "completed_date": [r"(?:Completed|Reported|Finalized|Date\s*Released|Released)\s*[:\s]+([0-9]{1,2}[/\-][0-9]{1,2}[/\-][0-9]{2,4})"],
    "received_date": [r"Received\s*[:\s]+([0-9]{1,2}[/\-][0-9]{1,2}[/\-][0-9]{2,4})"],
    "collected_date": [r"Collected\s*[:\s]+([0-9]{1,2}[/\-][0-9]{1,2}[/\-][0-9]{2,4})"],

    # Common potency summary fields
    "total_thc": [r"Total\s*THC[:\s]+([0-9]+(?:\.[0-9]+)?)\s*%"],
    "total_cbd": [r"Total\s*CBD[:\s]+([0-9]+(?:\.[0-9]+)?)\s*%"],
    "total_cannabinoids": [r"Total\s*Cannabinoids[:\s]+([0-9]+(?:\.[0-9]+)?)\s*%"],
    "moisture": [r"Moisture[:\s]+([0-9]+(?:\.[0-9]+)?)\s*%"],
    "water_activity": [r"Water\s*Activity[:\s]+([0-9]+(?:\.[0-9]+)?)\s*(?:aw)?"],

    # Real-world identifiers (e.g., GVA style)
    "metrc_sample_id": [r"METRC\s*Sample\s*ID[:\s]+([A-Z0-9]+)"],
    "metrc_source_package_id": [r"METRC\s*Source\s*Package\s*ID[:\s]+([A-Z0-9]+)"],
    "metrc_batch_id": [r"METRC\s*Batch\s*ID[:\s]+([A-Za-z0-9\-_]+)"],
    "order_id": [r"Order\s*#[:\s]+([A-Za-z0-9\-_]+)"],
    "report_number": [r"Report\s*#[:\s]+([A-Za-z0-9\-_]+)"],
    "license_client": [r"License\s*#[:\s]+(MC[0-9]+)"],
    "license_lab": [r"License\s*#[:\s]+(IL[0-9]+)"],
}

RD_QA_PATTERNS = [
    r"\bR&D\b",
    r"\bResearch\b",
    r"\bfor\s+research\s+only\b",
    r"\bQA\b\s*testing\b",
]

ISO_SCOPE_PATTERNS = [
    r"not\s+part\s+of.*ISO\s*17025\s*Scope",
    r"not\s+part\s+of.*Scope\s+of\s+Accreditation",
    r"outside\s+.*Scope\s+of\s+Accreditation",
]


# ============================
# ND / NT HANDLING
# ============================

ND_TOKENS = {"ND", "N.D.", "NOT DETECTED", "NON-DETECT", "NONDETECT"}
NT_TOKENS = {"NT", "N.T.", "NOT TESTED", "NOT ANALYZED"}

def normalize_token(s: str) -> str:
    return re.sub(r"\s+", " ", (s or "").strip().upper())

def is_nd_text(s: str) -> bool:
    t = normalize_token(s).replace(".", "")
    nd = {x.replace(".", "") for x in ND_TOKENS}
    return any(tok in t for tok in nd)

def is_nt_text(s: str) -> bool:
    t = normalize_token(s).replace(".", "")
    nt = {x.replace(".", "") for x in NT_TOKENS}
    return any(tok in t for tok in nt)

def has_nd_somewhere(per_page_text: List[str], panel: str) -> Optional[int]:
    """
    Returns a page index if the document appears to contain ND/Not Detected near panel keywords.
    This is NOT a pass/fail test; it’s a “helpful note”.
    """
    pats = PANEL_KEYWORDS.get(panel, [])
    for i, t in enumerate(per_page_text):
        if any(re.search(p, t, re.I) for p in pats) and re.search(r"\bND\b|Not\s+Detected|Non-Detect|Non\s*Detect", t, re.I):
            return i
    return None


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

def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

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
# TEXT EXTRACTION + OCR
# ============================

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


# ============================
# FIELD + PANEL DETECTION
# ============================

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


# ============================
# EVIDENCE HELPERS
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
    what_it_means: str
    evidence: Evidence
    recommendation: str

def find_first_match(per_page_text: List[str], patterns: List[str], max_snip: int = 240) -> Evidence:
    for i, t in enumerate(per_page_text):
        for pat in patterns:
            m = re.search(pat, t, flags=re.IGNORECASE)
            if m:
                start = max(m.start() - 80, 0)
                end = min(m.end() + 140, len(t))
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

def group_findings(findings: List[Finding]) -> Dict[str, List[Finding]]:
    out = {"HOLD": [], "WARN": [], "INFO": []}
    for f in findings:
        out.setdefault(f.severity, []).append(f)
    return out


# ============================
# DOMINANT CANNABINOIDS / TERPENES (robust-ish text scan)
# ============================

CANNABINOID_ALIASES: Dict[str, List[str]] = {
    "THCa": [r"\bTHCA\b", r"\bTHC-A\b"],
    "Δ9-THC": [r"Δ\s*9\s*-\s*THC", r"Delta\s*9\s*THC", r"\bD9\s*THC\b", r"\bΔ9THC\b"],
    "Δ8-THC": [r"Δ\s*8\s*-\s*THC", r"Delta\s*8\s*THC", r"\bD8\s*THC\b", r"\bΔ8THC\b"],
    "THCV": [r"\bTHCV\b"],
    "THCVa": [r"\bTHCVA\b", r"\bTHCV-A\b"],
    "CBDa": [r"\bCBDA\b", r"\bCBD-A\b"],
    "CBD": [r"\bCBD\b"],
    "CBG": [r"\bCBG\b"],
    "CBGa": [r"\bCBGA\b", r"\bCBG-A\b"],
    "CBC": [r"\bCBC\b"],
    "CBN": [r"\bCBN\b"],
}

TERPENE_ALIASES: Dict[str, List[str]] = {
    "Myrcene": [r"\bmyrcene\b", r"\bβ-?myrcene\b"],
    "Limonene": [r"\blimonene\b", r"\bd-?limonene\b"],
    "Caryophyllene": [r"\bcaryophyllene\b", r"\bβ-?caryophyllene\b"],
    "Humulene": [r"\bhumulene\b", r"\bα-?humulene\b"],
    "Pinene": [r"\bpinene\b", r"\bα-?pinene\b", r"\bβ-?pinene\b", r"\bbeta-?pinene\b"],
    "Linalool": [r"\blinalool\b"],
    "Terpinolene": [r"\bterpinolene\b"],
    "Ocimene": [r"\bocimene\b"],
    "Bisabolol": [r"\bbisabolol\b"],
    "Farnesene": [r"\bfarnesene\b"],
}

PCT_VALUE_RE = re.compile(r"(?P<val>\d+(?:\.\d+)?)\s*%")
MGG_VALUE_RE = re.compile(r"(?P<val>\d+(?:\.\d+)?)\s*(?:mg\/g|mgg)\b", flags=re.IGNORECASE)

def _best_numeric_from_line(line: str) -> Optional[float]:
    """
    Important: avoid mis-reading LOQ/LOD numbers on ND/NT rows.
    If a line indicates ND/NT, return None.
    Prefer percent. If no percent, accept mg/g (terpene tables sometimes do %; some do mg/g).
    """
    up = normalize_token(line)
    if is_nd_text(up) or re.search(r"\bND\b", up):
        return None
    if is_nt_text(up) or re.search(r"\bNT\b", up):
        return None

    m = PCT_VALUE_RE.search(line)
    if m:
        return float(m.group("val"))
    m2 = MGG_VALUE_RE.search(line)
    if m2:
        return float(m2.group("val"))
    return None

def parse_compounds_from_text(
    per_page_text: List[str],
    aliases: Dict[str, List[str]],
    max_hits_per_compound: int = 4,
) -> Dict[str, float]:
    """
    Scan lines; if a line contains a compound alias, capture the best numeric value.
    Keep the max value per compound (helps when it appears multiple times).
    """
    results: Dict[str, float] = {}
    seen_counts: Dict[str, int] = {k: 0 for k in aliases.keys()}

    for page in per_page_text:
        for raw_line in page.splitlines():
            line = raw_line.strip()
            if not line:
                continue

            for canonical, pats in aliases.items():
                if seen_counts[canonical] >= max_hits_per_compound:
                    continue
                if any(re.search(p, line, flags=re.IGNORECASE) for p in pats):
                    val = _best_numeric_from_line(line)
                    if val is None:
                        continue
                    prev = results.get(canonical)
                    results[canonical] = val if prev is None else max(prev, val)
                    seen_counts[canonical] += 1

    return results

def top_n(d: Dict[str, float], n: int = 3) -> List[Tuple[str, float]]:
    return sorted(d.items(), key=lambda kv: kv[1], reverse=True)[:n]


# ============================
# RULE ENGINE
# ============================

CONTAMINANT_PANELS = {"Pesticides", "Mycotoxins", "Microbials", "Heavy Metals", "Residual Solvents"}

def build_findings(
    *,
    state: str,
    product_type: str,
    fields: Dict[str, str],
    panels_detected: Dict[str, bool],
    per_page_text: List[str],
    freshness_days: int,
    d8_high_threshold_pct: float,
    d9_present_threshold_pct: float,
    parsed_cannabinoids_full: Dict[str, float],
    parsed_terpenes_full: Dict[str, float],
    dominant_cannabinoids: List[Tuple[str, float]],
    dominant_terpenes: List[Tuple[str, float]],
) -> List[Finding]:
    findings: List[Finding] = []

    required = REQUIRED_PANELS.get(state, {}).get(product_type, [])
    missing = [p for p in required if not panels_detected.get(p, False)]

    # HOLD: missing required panels
    for idx, p in enumerate(missing, start=1):
        findings.append(
            Finding(
                severity="HOLD",
                rule_id=f"{state}-MISS-PANEL-{idx:03d}",
                title=f"Required panel missing: {p}",
                what_it_means="The COA does not clearly show this required test panel in the extracted text. It may be missing or mislabeled.",
                evidence=Evidence(page_index=None, snippet=f"Panel '{p}' not detected in extracted document text."),
                recommendation="Request a corrected or complete COA that includes this panel with results, units, and method.",
            )
        )

    # WARN: R&D/QA language
    ev_rd = find_first_match(per_page_text, RD_QA_PATTERNS)
    if ev_rd.page_index is not None:
        findings.append(
            Finding(
                severity="WARN",
                rule_id=f"{state}-DOC-TYPE-001",
                title="Document language suggests R&D / QA context",
                what_it_means="Some COAs include non-compliance language; this can impact how the document is interpreted.",
                evidence=ev_rd,
                recommendation="Confirm whether a compliance-form COA is required and request it if necessary.",
            )
        )

    # WARN: ISO scope language
    ev_iso = find_first_match(per_page_text, ISO_SCOPE_PATTERNS)
    if ev_iso.page_index is not None:
        findings.append(
            Finding(
                severity="WARN",
                rule_id=f"{state}-ACCRED-001",
                title="Accreditation/scope limitation language detected",
                what_it_means="The COA may indicate some analytes are outside the lab’s accreditation scope, affecting how results are weighed.",
                evidence=ev_iso,
                recommendation="Review the lab scope statement and confirm which analytes are covered for your use-case.",
            )
        )

    # Freshness check (configurable)
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
                    title="COA date may be outside configured freshness threshold",
                    what_it_means="Older COAs may not represent the currently sold lot or may be less reliable for time-sensitive claims.",
                    evidence=Evidence(
                        page_index=ev_date.page_index,
                        snippet=f"Completed/Released date: {completed_raw} (~{age} days old). Threshold: {freshness_days} days.",
                    ),
                    recommendation="Request a more recent COA or document why this COA is acceptable.",
                )
            )
    elif freshness_days > 0:
        findings.append(
            Finding(
                severity="INFO",
                rule_id=f"{state}-FRESH-INFO-001",
                title="Completed/Released date not confidently extracted",
                what_it_means="The COA may contain the date, but it was not reliably detected in the extracted text.",
                evidence=Evidence(page_index=None, snippet="No completed/released date was reliably extracted."),
                recommendation="Verify the completed/released date manually on the COA.",
            )
        )

    # INFO: Dominant cannabinoids (top)
    if dominant_cannabinoids:
        top3 = ", ".join([f"{k} {v:.3f}%" for k, v in dominant_cannabinoids])
        findings.append(
            Finding(
                severity="INFO",
                rule_id=f"{state}-PROFILE-CAN-001",
                title="Dominant cannabinoids identified (top 3)",
                what_it_means="These are the most prominent cannabinoids detected from the COA tables (by %).",
                evidence=Evidence(page_index=None, snippet=top3),
                recommendation="Use this profile to compare lots and support product characterization.",
            )
        )

    # INFO: Dominant terpenes (top)
    if dominant_terpenes:
        top3t = ", ".join([f"{k} {v:.3f}%" for k, v in dominant_terpenes])
        findings.append(
            Finding(
                severity="INFO",
                rule_id=f"{state}-PROFILE-TERP-001",
                title="Dominant terpenes identified (top 3)",
                what_it_means="These are the most prominent terpenes detected from the COA tables (by %).",
                evidence=Evidence(page_index=None, snippet=top3t),
                recommendation="Use this terpene profile to compare lots and support aroma characterization.",
            )
        )

    # Option 2: Terpenes always reported as INFO for MA/NJ (optional)
    if "Terpenes" in OPTIONAL_PANELS_BY_STATE.get(state, []):
        if panels_detected.get("Terpenes"):
            ev = find_first_match(per_page_text, PANEL_KEYWORDS["Terpenes"])
            findings.append(
                Finding(
                    severity="INFO",
                    rule_id=f"{state}-TERP-INFO-001",
                    title="Terpenes panel detected (optional for this jurisdiction)",
                    what_it_means="Terpenes are being captured for reporting even when not required by the selected rule set.",
                    evidence=ev,
                    recommendation="None.",
                )
            )
        else:
            findings.append(
                Finding(
                    severity="INFO",
                    rule_id=f"{state}-TERP-INFO-002",
                    title="Terpenes panel not detected (optional for this jurisdiction)",
                    what_it_means="No terpene panel was detected; this does not block the report under the selected rule set.",
                    evidence=Evidence(page_index=None, snippet="No terpene panel keywords were detected in extracted text."),
                    recommendation="None.",
                )
            )

    # Helpful INFO: ND often indicates favorable for contaminant panels
    # (we do not “pass” the panel, we only add a note if ND language is found near the panel)
    for panel in sorted(CONTAMINANT_PANELS):
        if panels_detected.get(panel, False):
            pg = has_nd_somewhere(per_page_text, panel)
            if pg is not None:
                findings.append(
                    Finding(
                        severity="INFO",
                        rule_id=f"{state}-ND-NOTE-{panel.replace(' ', '').upper()[:10]}",
                        title=f"{panel}: ND/Not Detected language found (generally favorable)",
                        what_it_means="ND usually means the analyte was below the method detection limit (LOD).",
                        evidence=find_first_match(per_page_text, [r"\bND\b", r"Not\s+Detected"] + PANEL_KEYWORDS.get(panel, [])),
                        recommendation="Confirm any detected values are not present elsewhere on the COA tables.",
                    )
                )

    # WARN: high Δ8 while Δ9 present (oil products)
    if product_type in OIL_PRODUCT_TYPES:
        d8 = parsed_cannabinoids_full.get("Δ8-THC")
        d9 = parsed_cannabinoids_full.get("Δ9-THC")

        if d8 is None or d9 is None:
            findings.append(
                Finding(
                    severity="INFO",
                    rule_id=f"{state}-D8D9-INFO-001",
                    title="Δ8/Δ9 cross-check limited (values not confidently extracted)",
                    what_it_means="The COA may include these values, but text extraction did not produce reliable numbers.",
                    evidence=Evidence(page_index=None, snippet="Δ8-THC and/or Δ9-THC values were not reliably extracted."),
                    recommendation="Verify Δ8-THC and Δ9-THC rows manually on the COA cannabinoid table.",
                )
            )
        else:
            if d9 >= d9_present_threshold_pct and d8 >= d8_high_threshold_pct:
                ev = find_first_match(
                    per_page_text,
                    [r"(Δ\s*8\s*-\s*THC|Delta\s*8\s*THC|D8\s*THC)", r"(Δ\s*9\s*-\s*THC|Delta\s*9\s*THC|D9\s*THC)"]
                )
                findings.append(
                    Finding(
                        severity="WARN",
                        rule_id=f"{state}-D8D9-WARN-001",
                        title="Oil product: high Δ8-THC while Δ9-THC is also present",
                        what_it_means="Some jurisdictions and stakeholders treat unusually high Δ8 in oil products as a quality/compliance concern depending on context.",
                        evidence=Evidence(
                            page_index=ev.page_index,
                            snippet=f"Extracted: Δ8-THC {d8:.3f}% and Δ9-THC {d9:.3f}% (thresholds: Δ8 ≥ {d8_high_threshold_pct}%, Δ9 ≥ {d9_present_threshold_pct}%).",
                        ),
                        recommendation="Review process inputs, confirm units on the COA table, and validate whether this profile matches the product claims.",
                    )
                )

    return findings


# ============================
# PDF EXPORT — IMPROVED READABILITY
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

def draw_kv_table(c: canvas.Canvas, x: float, y: float, w: float, rows: List[Tuple[str, str]], col1_w: float = 140, row_h: float = 14) -> float:
    """
    Simple key/value table. Returns new y.
    """
    c.setFont("Helvetica", 10)
    for k, v in rows:
        # key
        c.setFont("Helvetica-Bold", 10)
        c.drawString(x, y, str(k))
        # value wrapped
        c.setFont("Helvetica", 10)
        y = wrap_text(c, str(v), x + col1_w, y, w - col1_w, size=10, leading=12)
        y -= 2
    return y

def draw_table(c: canvas.Canvas, x: float, y: float, w: float, headers: List[str], rows: List[List[str]],
               col_widths: List[float], row_h: float = 14, font_size: int = 9) -> float:
    """
    Lightweight table. No borders, but aligned columns.
    """
    c.setFont("Helvetica-Bold", font_size)
    cx = x
    for h, cw in zip(headers, col_widths):
        c.drawString(cx, y, h)
        cx += cw
    y -= row_h

    c.setFont("Helvetica", font_size)
    for r in rows:
        cx = x
        for cell, cw in zip(r, col_widths):
            txt = (cell or "").replace("\n", " ")
            # truncate to keep clean
            if len(txt) > 70 and cw < 220:
                txt = txt[:67] + "…"
            c.drawString(cx, y, txt)
            cx += cw
        y -= row_h
        if y < 0.9 * inch:
            c.showPage()
            y = letter[1] - 0.75 * inch
            c.setFont("Helvetica-Bold", font_size)
            cx = x
            for h, cw in zip(headers, col_widths):
                c.drawString(cx, y, h)
                cx += cw
            y -= row_h
            c.setFont("Helvetica", font_size)
    return y

def status_plain_language(findings: List[Finding]) -> str:
    """
    Make the top-line human.
    """
    status = overall_status(findings)
    if status == "PASS":
        return "No blocking issues were detected by the selected rule set. Review INFO notes for context."
    if status == "NEEDS REVIEW":
        return "Some items need attention. The COA may still be usable depending on your standards and context."
    return "Blocking issues were detected. This COA likely requires correction or additional documentation."

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
    dominant_cannabinoids: List[Tuple[str, float]],
    dominant_terpenes: List[Tuple[str, float]],
    parsed_cannabinoids_full: Dict[str, float],
    parsed_terpenes_full: Dict[str, float],
    source_file_bytes: bytes,
) -> bytes:
    buf = io.BytesIO()
    c = canvas.Canvas(buf, pagesize=letter)
    width, height = letter
    margin = 0.75 * inch
    x = margin
    y = height - margin
    max_w = width - 2 * margin

    generated_utc = utc_now_iso()
    status = overall_status(findings)
    grouped = group_findings(findings)

    # ==============
    # Page 1: Executive Summary (scannable)
    # ==============
    c.setFont("Helvetica-Bold", 18)
    c.drawString(x, y, f"{APP_NAME} — COA Summary Report")
    y -= 20

    c.setFont("Helvetica", 10)
    c.drawString(x, y, f"Record ID: {record_id}")
    y -= 12
    c.drawString(x, y, f"Generated (UTC): {generated_utc}")
    y -= 12
    c.drawString(x, y, f"Reviewer: {uploader or 'Not provided'}")
    y -= 12
    c.drawString(x, y, f"Jurisdiction: {state}   |   Product Type: {product_type}")
    y -= 12
    c.drawString(x, y, f"Ruleset: {ruleset_version}   |   App: {APP_VERSION}")
    y -= 12
    c.drawString(x, y, f"Parsing: {parsing_method}   |   OCR confidence: {('N/A' if ocr_confidence is None else f'{ocr_confidence:.1f}/100')}")
    y -= 16

    c.setFont("Helvetica-Bold", 14)
    c.drawString(x, y, f"Overall Result: {status}")
    y -= 14
    c.setFont("Helvetica", 10)
    y = wrap_text(c, status_plain_language(findings), x, y, max_w, size=10, leading=12)
    y -= 8

    # Counts in plain English
    c.setFont("Helvetica-Bold", 11)
    c.drawString(x, y, "Issue Counts")
    y -= 14
    c.setFont("Helvetica", 10)
    c.drawString(x, y, f"HOLD (blocking): {len(grouped['HOLD'])}   |   WARN (review): {len(grouped['WARN'])}   |   INFO (notes): {len(grouped['INFO'])}")
    y -= 18

    # Profile summary block
    c.setFont("Helvetica-Bold", 11)
    c.drawString(x, y, "Profile Summary")
    y -= 14
    c.setFont("Helvetica", 10)
    if dominant_cannabinoids:
        y = wrap_text(c, "Dominant cannabinoids (top 3): " + ", ".join([f"{k} {v:.3f}%" for k, v in dominant_cannabinoids]), x, y, max_w)
    else:
        y = wrap_text(c, "Dominant cannabinoids (top 3): Not reliably extracted.", x, y, max_w)
    if dominant_terpenes:
        y = wrap_text(c, "Dominant terpenes (top 3): " + ", ".join([f"{k} {v:.3f}%" for k, v in dominant_terpenes]), x, y, max_w)
    else:
        y = wrap_text(c, "Dominant terpenes (top 3): Not reliably extracted / not reported.", x, y, max_w)
    y -= 10

    # Key identifiers table
    c.setFont("Helvetica-Bold", 11)
    c.drawString(x, y, "Key Identifiers (as extracted)")
    y -= 14

    id_rows = [
        ("Source file", source_filename),
        ("Source SHA-256", source_sha256),
        ("File size", f"{source_size_bytes} bytes"),
        ("Lab", fields.get("lab_name", "Not detected")),
        ("Report #", fields.get("report_number", "Not detected")),
        ("Order #", fields.get("order_id", "Not detected")),
        ("Sample ID", fields.get("sample_id", "Not detected")),
        ("Batch/Lot", fields.get("batch_id", "Not detected")),
        ("METRC sample ID", fields.get("metrc_sample_id", "Not detected")),
        ("METRC source package ID", fields.get("metrc_source_package_id", "Not detected")),
        ("METRC batch ID", fields.get("metrc_batch_id", "Not detected")),
        ("Client license", fields.get("license_client", "Not detected")),
        ("Lab license", fields.get("license_lab", "Not detected")),
        ("Collected", fields.get("collected_date", "Not detected")),
        ("Received", fields.get("received_date", "Not detected")),
        ("Completed/Released", fields.get("completed_date", "Not detected")),
    ]
    y = draw_kv_table(c, x, y, max_w, id_rows, col1_w=165)
    y -= 8

    # If page is tight, start new page before panels
    if y < 2.0 * inch:
        c.showPage()
        y = height - margin

    # Panel checklist
    c.setFont("Helvetica-Bold", 11)
    c.drawString(x, y, "Panel Checklist")
    y -= 14

    required = REQUIRED_PANELS.get(state, {}).get(product_type, [])
    optional = OPTIONAL_PANELS_BY_STATE.get(state, [])

    panel_rows: List[List[str]] = []
    for p in required:
        panel_rows.append([p, "REQUIRED", "Yes" if panels_detected.get(p, False) else "No"])
    for p in optional:
        panel_rows.append([p, "OPTIONAL", "Yes" if panels_detected.get(p, False) else "No"])

    y = draw_table(
        c, x, y, max_w,
        headers=["Panel", "Rule", "Detected in text"],
        rows=panel_rows,
        col_widths=[260, 110, 140],
        row_h=14,
        font_size=9
    )
    y -= 6

    # ==============
    # Page 2: Issues in plain language (table)
    # ==============
    c.showPage()
    y = height - margin

    c.setFont("Helvetica-Bold", 14)
    c.drawString(x, y, "Issues & Recommendations (Plain Language)")
    y -= 18

    # Put HOLD then WARN then INFO
    def findings_to_rows(items: List[Finding]) -> List[List[str]]:
        rows = []
        for f in items:
            pg = "N/A" if f.evidence.page_index is None else str(f.evidence.page_index + 1)
            rows.append([
                f.severity,
                f.title,
                f.what_it_means,
                f.recommendation,
                f"p.{pg}: {f.evidence.snippet}",
            ])
        return rows

    all_rows: List[List[str]] = []
    for sev in ["HOLD", "WARN", "INFO"]:
        all_rows.extend(findings_to_rows(grouped.get(sev, [])))

    if not all_rows:
        c.setFont("Helvetica", 11)
        c.drawString(x, y, "No issues were generated by the current rule set.")
        y -= 14
    else:
        y = draw_table(
            c, x, y, max_w,
            headers=["Level", "Issue", "What it means", "Recommendation", "Evidence"],
            rows=all_rows,
            col_widths=[55, 120, 140, 140, 135],
            row_h=14,
            font_size=8
        )

    # ==============
    # Page 3: Extracted profiles (top lists + full maps as compact tables)
    # ==============
    c.showPage()
    y = height - margin

    c.setFont("Helvetica-Bold", 14)
    c.drawString(x, y, "Extracted Cannabinoid & Terpene Data")
    y -= 18

    c.setFont("Helvetica-Bold", 11)
    c.drawString(x, y, "Dominant Cannabinoids (Top 3)")
    y -= 14
    can_top_rows = [[k, f"{v:.3f}%"] for k, v in (dominant_cannabinoids or [])]
    if not can_top_rows:
        can_top_rows = [["Not reliably extracted", ""]]
    y = draw_table(c, x, y, max_w, ["Cannabinoid", "Value"], can_top_rows, [220, 120], row_h=14, font_size=10)
    y -= 8

    c.setFont("Helvetica-Bold", 11)
    c.drawString(x, y, "Dominant Terpenes (Top 3)")
    y -= 14
    terp_top_rows = [[k, f"{v:.3f}%"] for k, v in (dominant_terpenes or [])]
    if not terp_top_rows:
        terp_top_rows = [["Not reliably extracted / not reported", ""]]
    y = draw_table(c, x, y, max_w, ["Terpene", "Value"], terp_top_rows, [220, 120], row_h=14, font_size=10)
    y -= 12

    # Full extracted maps (compact)
    c.setFont("Helvetica-Bold", 11)
    c.drawString(x, y, "All Extracted Cannabinoids (from text scan)")
    y -= 14
    all_can = sorted(parsed_cannabinoids_full.items(), key=lambda kv: kv[1], reverse=True)
    can_rows = [[k, f"{v:.3f}%"] for k, v in all_can[:25]]  # cap to keep readable
    if not can_rows:
        can_rows = [["None extracted", ""]]
    y = draw_table(c, x, y, max_w, ["Cannabinoid", "Value"], can_rows, [220, 120], row_h=13, font_size=9)
    y -= 10

    if y < 2.0 * inch:
        c.showPage()
        y = height - margin

    c.setFont("Helvetica-Bold", 11)
    c.drawString(x, y, "All Extracted Terpenes (from text scan)")
    y -= 14
    all_terp = sorted(parsed_terpenes_full.items(), key=lambda kv: kv[1], reverse=True)
    terp_rows = [[k, f"{v:.3f}%"] for k, v in all_terp[:30]]
    if not terp_rows:
        terp_rows = [["None extracted / not reported", ""]]
    y = draw_table(c, x, y, max_w, ["Terpene", "Value"], terp_rows, [220, 120], row_h=13, font_size=9)
    y -= 12

    # ==============
    # Glossary + methods
    # ==============
    c.showPage()
    y = height - margin
    c.setFont("Helvetica-Bold", 14)
    c.drawString(x, y, "Glossary & Methods")
    y -= 18

    c.setFont("Helvetica-Bold", 11)
    c.drawString(x, y, "Key Terms")
    y -= 14
    c.setFont("Helvetica", 10)
    y = wrap_text(c, "ND (Not Detected): The analyte was not detected above the lab’s detection limit (LOD). This is generally favorable for contaminants.", x, y, max_w)
    y = wrap_text(c, "NT (Not Tested): The analyte/panel was not tested. This is different from ND and may require follow-up depending on the rule set.", x, y, max_w)
    y = wrap_text(c, "LOD/LOQ: Limits related to detection and quantitation. Leafline tries to avoid misreading LOD/LOQ values as analyte results.", x, y, max_w)
    y -= 10

    c.setFont("Helvetica-Bold", 11)
    c.drawString(x, y, "Methods & Limitations")
    y -= 14
    c.setFont("Helvetica", 10)
    method_text = (
        f"{APP_NAME} extracts text from the uploaded COA (PDF text when available; OCR when needed) and applies the selected jurisdiction rule set. "
        "Results reflect what was detected in the document text at the time of report generation. "
        "This report does not validate authenticity, sampling integrity, or lab methodology beyond the document provided. "
        "If OCR was used, text may contain errors. A missing panel finding means the panel was not detected in extracted text and may require manual verification."
    )
    y = wrap_text(c, method_text, x, y, max_w)
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
        y = wrap_text(c, line, x, y, max_w)

    # ==============
    # Evidence Appendix: embed referenced pages (PDF only)
    # ==============
    appendix_items = [f for f in findings if f.evidence.page_index is not None]
    if appendix_items and source_file_bytes:
        c.showPage()
        y = height - margin
        c.setFont("Helvetica-Bold", 14)
        c.drawString(x, y, "Evidence Appendix (Referenced COA Pages)")
        y -= 18
        c.setFont("Helvetica", 10)
        y = wrap_text(
            c,
            "For issues with a detected page reference, the corresponding COA page image is embedded on the next pages.",
            x, y, max_w
        )

        for fnd in appendix_items:
            pg = fnd.evidence.page_index
            c.showPage()
            y = height - margin
            c.setFont("Helvetica-Bold", 12)
            c.drawString(x, y, f"{fnd.severity}: {fnd.title}")
            y -= 14
            c.setFont("Helvetica", 10)
            c.drawString(x, y, f"Referenced page: {pg + 1}")
            y -= 12
            y = wrap_text(c, f"Snippet: {fnd.evidence.snippet}", x, y, max_w)
            y -= 8

            try:
                page_img = render_pdf_page_image(source_file_bytes, pg, zoom=2.0)
                max_img_w = width - 2 * margin
                max_img_h = height - 2 * margin - 90
                iw, ih = page_img.size
                scale = min(max_img_w / iw, max_img_h / ih)
                dw, dh = iw * scale, ih * scale
                c.drawImage(ImageReader(page_img), x, margin, width=dw, height=dh, preserveAspectRatio=True, mask="auto")
            except Exception:
                c.drawString(x, y, "Unable to embed page image (rendering error).")

    c.save()
    return buf.getvalue()


# ============================
# STREAMLIT UI
# ============================

st.set_page_config(page_title="Leafline — COA Analyzer", layout="wide")
init_db()

st.title("Leafline — COA Analyzer")
st.caption("Upload a COA to extract key details, identify dominant cannabinoids/terpenes, apply state rules, and export a clean PDF report.")

# Optional access gate (Streamlit secrets)
if "LEAFLINE_PASSWORD" in st.secrets:
    pw = st.text_input("Access password", type="password")
    if pw != st.secrets["LEAFLINE_PASSWORD"]:
        st.stop()

col1, col2, col3, col4 = st.columns([1, 1, 1, 1])
with col1:
    state = st.selectbox("Jurisdiction", STATE_OPTIONS, index=0)
with col2:
    product_type = st.selectbox("Product type", PRODUCT_TYPES, index=0)
with col3:
    freshness_days = st.number_input("Freshness threshold (days)", min_value=0, max_value=3650, value=365, step=30)
with col4:
    st.markdown("**Δ8/Δ9 flag (oil products)**")

c1, c2 = st.columns([1, 1])
with c1:
    d8_high_threshold_pct = st.number_input("Δ8 high threshold (%)", min_value=0.0, max_value=100.0, value=5.0, step=0.5)
with c2:
    d9_present_threshold_pct = st.number_input("Δ9 present threshold (%)", min_value=0.0, max_value=100.0, value=0.5, step=0.1)

uploader = st.text_input("Reviewer identifier (optional)", value="")

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

    is_pdf = uploaded.name.lower().endswith(".pdf")
    parsing_method = ""
    ocr_conf = None
    extracted_text = ""
    per_page_text: List[str] = []

    with st.spinner("Extracting text..."):
        if is_pdf:
            extracted_text, per_page_text = extract_text_from_pdf(file_bytes)
            # If PDF text is too thin, OCR
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

    # Audit log
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

    fields = extract_fields(extracted_text)
    panels_detected = detect_panels(extracted_text)

    # Parse compounds (ND/NT lines ignored)
    parsed_cannabinoids_full = parse_compounds_from_text(per_page_text, CANNABINOID_ALIASES)
    parsed_terpenes_full = parse_compounds_from_text(per_page_text, TERPENE_ALIASES)

    dominant_cannabinoids = top_n(parsed_cannabinoids_full, n=3)
    dominant_terpenes = top_n(parsed_terpenes_full, n=3)

    findings = build_findings(
        state=state,
        product_type=product_type,
        fields=fields,
        panels_detected=panels_detected,
        per_page_text=per_page_text,
        freshness_days=int(freshness_days),
        d8_high_threshold_pct=float(d8_high_threshold_pct),
        d9_present_threshold_pct=float(d9_present_threshold_pct),
        parsed_cannabinoids_full=parsed_cannabinoids_full,
        parsed_terpenes_full=parsed_terpenes_full,
        dominant_cannabinoids=dominant_cannabinoids,
        dominant_terpenes=dominant_terpenes,
    )

    status = overall_status(findings)
    grouped = group_findings(findings)

    # ============================
    # ON-SCREEN SUMMARY (BEFORE EXPORT)
    # ============================
    st.subheader("COA Summary (Review before export)")

    s1, s2, s3, s4 = st.columns(4)
    s1.metric("Overall Result", status)
    s2.metric("HOLD", len(grouped["HOLD"]))
    s3.metric("WARN", len(grouped["WARN"]))
    s4.metric("INFO", len(grouped["INFO"]))

    a1, a2 = st.columns(2)
    with a1:
        st.markdown("**Dominant cannabinoids (top 3):**")
        if dominant_cannabinoids:
            st.table([{"Cannabinoid": k, "Value (%)": round(v, 3)} for k, v in dominant_cannabinoids])
        else:
            st.write("Not reliably extracted.")
    with a2:
        st.markdown("**Dominant terpenes (top 3):**")
        if dominant_terpenes:
            st.table([{"Terpene": k, "Value (%)": round(v, 3)} for k, v in dominant_terpenes])
        else:
            st.write("Not reliably extracted / not reported.")

    st.markdown("**Key identifiers (as extracted):**")
    st.json({
        "lab": fields.get("lab_name", "Not detected"),
        "report_number": fields.get("report_number", "Not detected"),
        "order_id": fields.get("order_id", "Not detected"),
        "sample_id": fields.get("sample_id", "Not detected"),
        "batch_id": fields.get("batch_id", "Not detected"),
        "metrc_sample_id": fields.get("metrc_sample_id", "Not detected"),
        "metrc_source_package_id": fields.get("metrc_source_package_id", "Not detected"),
        "metrc_batch_id": fields.get("metrc_batch_id", "Not detected"),
        "client_license": fields.get("license_client", "Not detected"),
        "lab_license": fields.get("license_lab", "Not detected"),
        "collected_date": fields.get("collected_date", "Not detected"),
        "received_date": fields.get("received_date", "Not detected"),
        "completed_released_date": fields.get("completed_date", "Not detected"),
    })

    st.markdown("**Panels detected (text-based):**")
    st.json(panels_detected)

    st.subheader("Issues & Recommendations (Preview)")
    if not findings:
        st.success("No issues generated by current rule set.")
    else:
        for sev in ["HOLD", "WARN", "INFO"]:
            items = grouped.get(sev, [])
            if not items:
                continue
            with st.expander(f"{sev} ({len(items)})", expanded=(sev in ["HOLD", "WARN"])):
                for f in items:
                    pg = "N/A" if f.evidence.page_index is None else str(f.evidence.page_index + 1)
                    st.markdown(f"**{f.rule_id} — {f.title}**")
                    st.markdown(f"- What it means: {f.what_it_means}")
                    st.markdown(f"- Recommendation: {f.recommendation}")
                    st.markdown(f"- Evidence (page {pg}): {f.evidence.snippet}")

    with st.expander("All extracted cannabinoids (debug)", expanded=False):
        st.json(parsed_cannabinoids_full or {})
    with st.expander("All extracted terpenes (debug)", expanded=False):
        st.json(parsed_terpenes_full or {})
    with st.expander("Extracted text (debug)", expanded=False):
        st.text(extracted_text[:25000] if extracted_text else "No text extracted.")

    export_ready = st.checkbox("I reviewed the summary above and want to generate the PDF report.", value=True)

    if export_ready:
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
            dominant_cannabinoids=dominant_cannabinoids,
            dominant_terpenes=dominant_terpenes,
            parsed_cannabinoids_full=parsed_cannabinoids_full,
            parsed_terpenes_full=parsed_terpenes_full,
            source_file_bytes=file_bytes if is_pdf else b"",
        )

        report_sha = sha256_bytes(pdf_bytes)
        db_insert_event(record_id, "REPORT_GENERATED", {
            "report_sha256": report_sha,
            "overall_status": status,
            "finding_count": len(findings),
            "ruleset_version": ruleset_version,
            "app_version": APP_VERSION,
        })

        st.write(f"**Report SHA-256:** `{report_sha}`")

        st.download_button(
            label="Download PDF Report",
            data=pdf_bytes,
            file_name=f"Leafline_Report_{state}_{product_type}_{record_id}.pdf",
            mime="application/pdf",
        )
else:
    st.info("Upload a COA to generate a summary and PDF report.")
