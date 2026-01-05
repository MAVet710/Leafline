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
from PIL import Image
import pytesseract
from dateutil import parser as dateparser

from reportlab.lib.pagesizes import letter
from reportlab.lib.units import inch
from reportlab.pdfgen import canvas

# ============================
# APP META
# ============================
APP_NAME = "Leafline"
APP_VERSION = "1.3.0"
DB_PATH = "leafline_audit.db"

STATE_OPTIONS = ["MA", "NY", "NJ"]
PRODUCT_TYPES = ["Flower", "Pre-roll", "Concentrate", "Vape", "Edible", "Topical", "Tincture"]
OIL_PRODUCT_TYPES = {"Concentrate", "Vape", "Tincture"}

# ============================
# RULE PACKS (STARTER)
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

# Terpenes: NY required; MA/NJ optional but we still report if present
OPTIONAL_PANELS_BY_STATE = {"MA": ["Terpenes"], "NJ": ["Terpenes"], "NY": []}

# ============================
# DETECTION KEYWORDS
# ============================
PANEL_KEYWORDS = {
    "Cannabinoids": [r"\bcannabinoid", r"\bpotency", r"Total\s+THC", r"Total\s+CBD", r"\bTHC\b", r"\bCBD\b"],
    "Terpenes": [r"\bterpene", r"\blimonene\b", r"\bmyrcene\b", r"\bcaryophyllene\b", r"\bpinene\b", r"\blinalool\b"],
    "Moisture": [r"\bmoisture\b"],
    "Water Activity": [r"\bwater\s*activity\b", r"\baw\b"],
    "Microbials": [r"\bmicrobial", r"\bE\.\s*coli\b", r"\bsalmonella\b", r"\byeast\b", r"\bmold\b"],
    "Mycotoxins": [r"\bmycotoxin", r"\baflatoxin\b", r"\bochratoxin\b"],
    "Pesticides": [r"\bpesticide"],
    "Heavy Metals": [r"\bheavy\s*metals?\b", r"\blead\b", r"\barsenic\b", r"\bcadmium\b", r"\bmercury\b"],
    "Residual Solvents": [r"\bsolvent", r"\bresidual\s*solvent", r"\bbutane\b", r"\bpropane\b", r"\bethanol\b"],
    "Foreign Matter": [r"\bforeign\s*matter\b", r"\bvisual\s*inspection\b"],
}

FIELD_PATTERNS = {
    "lab_name": [r"Encore\s+Labs|Lab\s*Name[:\s]+(.+)"],
    "sample_id": [r"Sample\s*(?:#|ID)[:\s]+([A-Za-z0-9\-_]+)"],
    "batch_id": [r"Batch\s*(?:#|No\.|Number|ID)?[:\s]+([A-Za-z0-9\-_]+)", r"Lot\s*(?:#|No\.)?[:\s]+([A-Za-z0-9\-_]+)"],
    "matrix": [r"Matrix[:\s]+(.+)", r"Sample\s*Type[:\s]+(.+)", r"Product\s*Type[:\s]+(.+)"],
    "completed_date": [r"(?:Completed|Reported|Finalized|Date\s*Released|Released)\s*[:\s]+([0-9]{1,2}[/\-][0-9]{1,2}[/\-][0-9]{2,4})"],
    "received_date": [r"Received\s*[:\s]+([0-9]{1,2}[/\-][0-9]{1,2}[/\-][0-9]{2,4})"],
    "collected_date": [r"Collected\s*[:\s]+([0-9]{1,2}[/\-][0-9]{1,2}[/\-][0-9]{2,4})"],
    "total_thc": [r"Total\s*THC[:\s]+([0-9]+(?:\.[0-9]+)?)\s*%"],
    "total_cbd": [r"Total\s*CBD[:\s]+([0-9]+(?:\.[0-9]+)?)\s*%"],
    "total_cannabinoids": [r"Total\s*Cannabinoids[:\s]+([0-9]+(?:\.[0-9]+)?)\s*%"],
}

RD_QA_PATTERNS = [r"\bR&D\b", r"\bQA\b", r"\bfor\s+research\s+only\b"]
ISO_SCOPE_PATTERNS = [r"not\s+part\s+of.*ISO\s*17025\s*Scope", r"outside\s+.*Scope\s+of\s+Accreditation"]

# ============================
# ND / NT / LOQ
# ============================
def normalize_token(s: str) -> str:
    return re.sub(r"\s+", " ", (s or "").strip().upper())

def is_nd(s: str) -> bool:
    t = normalize_token(s).replace(".", "")
    return any(x in t for x in ["ND", "NOT DETECTED", "NONDETECT", "NON-DETECT"])

def is_nt(s: str) -> bool:
    t = normalize_token(s).replace(".", "")
    return any(x in t for x in ["NT", "NOT TESTED", "NOT ANALYZED"])

def is_loq(s: str) -> bool:
    t = normalize_token(s)
    return "<LOQ" in t or "BELOW LOQ" in t or "LESS THAN LOQ" in t

# ============================
# AUDIT DB
# ============================
def init_db():
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute("""
    CREATE TABLE IF NOT EXISTS records (
        record_id TEXT PRIMARY KEY,
        created_at_utc TEXT NOT NULL,
        reviewer TEXT,
        source_filename TEXT NOT NULL,
        source_sha256 TEXT NOT NULL,
        source_size_bytes INTEGER NOT NULL,
        state TEXT NOT NULL,
        product_type TEXT NOT NULL,
        ruleset_version TEXT NOT NULL,
        parsing_method TEXT NOT NULL,
        notes TEXT
    )
    """)
    cur.execute("""
    CREATE TABLE IF NOT EXISTS events (
        event_id TEXT PRIMARY KEY,
        record_id TEXT NOT NULL,
        event_type TEXT NOT NULL,
        event_at_utc TEXT NOT NULL,
        event_payload TEXT
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
        record_id, created_at_utc, reviewer, source_filename, source_sha256, source_size_bytes,
        state, product_type, ruleset_version, parsing_method, notes
    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    """, (
        row["record_id"], row["created_at_utc"], row.get("reviewer"),
        row["source_filename"], row["source_sha256"], row["source_size_bytes"],
        row["state"], row["product_type"], row["ruleset_version"],
        row["parsing_method"], row.get("notes")
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
# EXTRACTION
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

def ocr_image(img_bytes: bytes) -> str:
    img = Image.open(io.BytesIO(img_bytes))
    return pytesseract.image_to_string(img)

def extract_fields(text: str) -> Dict[str, str]:
    out: Dict[str, str] = {}
    for field, patterns in FIELD_PATTERNS.items():
        for pat in patterns:
            m = re.search(pat, text, flags=re.IGNORECASE | re.MULTILINE)
            if m:
                out[field] = m.group(1).strip() if m.groups() else m.group(0).strip()
                break
    return out

def detect_panels(text: str) -> Dict[str, bool]:
    detected = {}
    for panel, pats in PANEL_KEYWORDS.items():
        detected[panel] = any(re.search(p, text, flags=re.IGNORECASE) for p in pats)
    return detected

# ============================
# TABLE-FIRST % COLUMN PARSING
# ============================
def _clean_cell(x) -> str:
    return re.sub(r"\s+", " ", ("" if x is None else str(x)).strip())

def _to_float_pct(cell: str) -> Optional[float]:
    if not cell:
        return None
    if is_nd(cell) or is_nt(cell) or is_loq(cell):
        return None
    s = cell.replace("%", "").strip()
    try:
        return float(s)
    except Exception:
        return None

def _find_col_idx(headers: List[str], candidates: List[str]) -> Optional[int]:
    norm = [re.sub(r"\s+", "", h).lower() for h in headers]
    for cand in candidates:
        c = re.sub(r"\s+", "", cand).lower()
        for i, h in enumerate(norm):
            if h == c:
                return i
    return None

def extract_percent_tables_from_pdf(pdf_bytes: bytes) -> Dict[str, Dict[str, float]]:
    results: Dict[str, Dict[str, float]] = {}

    table_settings = {
        "vertical_strategy": "lines",
        "horizontal_strategy": "lines",
        "snap_tolerance": 3,
        "join_tolerance": 3,
        "edge_min_length": 3,
        "min_words_vertical": 1,
        "min_words_horizontal": 1,
        "intersection_tolerance": 3,
    }

    with pdfplumber.open(io.BytesIO(pdf_bytes)) as pdf:
        for page in pdf.pages:
            try:
                tables = page.extract_tables(table_settings=table_settings) or []
            except Exception:
                tables = page.extract_tables() or []

            page_text = (page.extract_text() or "").lower()

            for t in tables:
                if not t or len(t) < 2:
                    continue

                headers = [_clean_cell(h) for h in t[0]]
                if not any(headers):
                    continue

                pct_idx = _find_col_idx(headers, ["%", "percent", "pct"])
                if pct_idx is None:
                    continue

                compound_idx = _find_col_idx(headers, ["compound", "analyte", "analytes", "name"])
                if compound_idx is None:
                    compound_idx = 0

                section = "Analytes"
                if "cannabinoid" in page_text or any("cannabino" in h.lower() for h in headers):
                    section = "Cannabinoids"
                elif "terpene" in page_text or any("terp" in h.lower() for h in headers):
                    section = "Terpenes"
                elif "pesticide" in page_text:
                    section = "Pesticides"
                elif "mycotoxin" in page_text:
                    section = "Mycotoxins"
                elif "metal" in page_text:
                    section = "Heavy Metals"
                elif "solvent" in page_text:
                    section = "Residual Solvents"
                elif "micro" in page_text or "yeast" in page_text or "mold" in page_text:
                    section = "Microbials"

                section_map = results.setdefault(section, {})

                for row in t[1:]:
                    if not row or len(row) <= max(compound_idx, pct_idx):
                        continue

                    compound = _clean_cell(row[compound_idx])
                    pct_cell = _clean_cell(row[pct_idx])

                    if not compound:
                        continue

                    val = _to_float_pct(pct_cell)
                    if val is None:
                        continue

                    section_map[compound] = max(section_map.get(compound, 0.0), val)

    return results

# ============================
# FALLBACK LINE PARSER
# ============================
PCT_VALUE_RE = re.compile(r"(\d+(?:\.\d+)?)\s*%")

def parse_pct_from_line(line: str) -> Optional[float]:
    if is_nd(line) or is_nt(line) or is_loq(line):
        return None
    m = PCT_VALUE_RE.search(line)
    if not m:
        return None
    try:
        return float(m.group(1))
    except Exception:
        return None

def parse_compounds_by_percent(per_page_text: List[str], aliases: Dict[str, List[str]]) -> Dict[str, float]:
    out: Dict[str, float] = {}
    for page in per_page_text:
        for raw_line in page.splitlines():
            line = raw_line.strip()
            if not line:
                continue
            for canonical, pats in aliases.items():
                if any(re.search(p, line, flags=re.IGNORECASE) for p in pats):
                    val = parse_pct_from_line(line)
                    if val is None:
                        continue
                    out[canonical] = max(out.get(canonical, 0.0), val)
    return out

def rank_profile(vals: Dict[str, float]) -> List[Tuple[str, float]]:
    return sorted(vals.items(), key=lambda kv: kv[1], reverse=True)

def bucket_cannabinoids(ranked: List[Tuple[str, float]]) -> Dict[str, List[Tuple[str, float]]]:
    buckets = {"Dominant": [], "Secondary": [], "Minor": []}
    for name, v in ranked:
        if v >= 10.0:
            buckets["Dominant"].append((name, v))
        elif v >= 1.0:
            buckets["Secondary"].append((name, v))
        elif v >= 0.1:
            buckets["Minor"].append((name, v))
    return buckets

def bucket_terpenes(ranked: List[Tuple[str, float]]) -> Dict[str, List[Tuple[str, float]]]:
    buckets = {"Dominant": [], "Secondary": [], "Minor": []}
    for name, v in ranked:
        if v >= 0.5:
            buckets["Dominant"].append((name, v))
        elif v >= 0.1:
            buckets["Secondary"].append((name, v))
        else:
            buckets["Minor"].append((name, v))
    return buckets

# ============================
# ALIASES (fallback only)
# ============================
CANNABINOID_ALIASES: Dict[str, List[str]] = {
    "THCa": [r"\bTHCA\b", r"\bTHC-A\b"],
    "Δ9-THC": [r"Δ\s*9\s*-\s*THC", r"Delta\s*9\s*THC", r"\bD9\s*THC\b", r"\bΔ9THC\b", r"\bd9-THC\b"],
    "Δ8-THC": [r"Δ\s*8\s*-\s*THC", r"Delta\s*8\s*THC", r"\bD8\s*THC\b", r"\bΔ8THC\b", r"\bd8-THC\b"],
    "THCV": [r"\bTHCV\b"],
    "CBDa": [r"\bCBDA\b", r"\bCBD-A\b"],
    "CBD": [r"\bCBD\b"],
    "CBG": [r"\bCBG\b"],
    "CBC": [r"\bCBC\b"],
    "CBN": [r"\bCBN\b"],
}

TERPENE_ALIASES: Dict[str, List[str]] = {
    "Myrcene": [r"\bmyrcene\b"],
    "Limonene": [r"\blimonene\b"],
    "Caryophyllene": [r"\bcaryophyllene\b"],
    "Humulene": [r"\bhumulene\b"],
    "Pinene": [r"\bpinene\b"],
    "Linalool": [r"\blinalool\b"],
    "Terpinolene": [r"\bterpinolene\b"],
    "Ocimene": [r"\bocimene\b"],
    "Bisabolol": [r"\bbisabolol\b"],
    "Farnesene": [r"\bfarnesene\b"],
}

# ============================
# EVIDENCE + FINDINGS
# ============================
@dataclass
class Evidence:
    page_index: Optional[int]
    snippet: str

@dataclass
class Finding:
    severity: str  # HOLD, WARN, INFO
    rule_id: str
    title: str
    meaning: str
    recommendation: str
    evidence: Evidence

def find_first_match(per_page_text: List[str], patterns: List[str], max_snip: int = 220) -> Evidence:
    for i, t in enumerate(per_page_text):
        for pat in patterns:
            m = re.search(pat, t, flags=re.IGNORECASE)
            if m:
                start = max(m.start() - 70, 0)
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

CONTAMINANT_PANELS = {"Pesticides", "Mycotoxins", "Microbials", "Heavy Metals", "Residual Solvents"}

def panel_has_nd(per_page_text: List[str], panel: str) -> bool:
    pats = PANEL_KEYWORDS.get(panel, [])
    for t in per_page_text:
        if any(re.search(p, t, re.I) for p in pats) and re.search(r"\bND\b|Not\s+Detected|Non-Detect|Non\s*Detect", t, re.I):
            return True
    return False

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
    cannabinoids_pct: Dict[str, float],
) -> List[Finding]:
    findings: List[Finding] = []
    required = REQUIRED_PANELS.get(state, {}).get(product_type, [])
    missing = [p for p in required if not panels_detected.get(p, False)]

    for i, p in enumerate(missing, start=1):
        findings.append(Finding(
            severity="HOLD",
            rule_id=f"{state}-REQ-{i:03d}",
            title=f"Required panel missing: {p}",
            meaning="This panel was not detected in the extracted COA text. It may be missing or labeled differently.",
            recommendation="Request a complete COA that clearly includes this panel and its results.",
            evidence=Evidence(page_index=None, snippet=f"Panel '{p}' not detected in extracted text.")
        ))

    ev_rd = find_first_match(per_page_text, RD_QA_PATTERNS)
    if ev_rd.page_index is not None:
        findings.append(Finding(
            severity="WARN",
            rule_id=f"{state}-DOC-001",
            title="R&D / QA language detected",
            meaning="Some COAs contain R&D/QA wording that can change how the document is interpreted.",
            recommendation="Confirm whether a compliance-format COA is required.",
            evidence=ev_rd
        ))

    ev_iso = find_first_match(per_page_text, ISO_SCOPE_PATTERNS)
    if ev_iso.page_index is not None:
        findings.append(Finding(
            severity="WARN",
            rule_id=f"{state}-ACC-001",
            title="Scope/accreditation limitation language detected",
            meaning="The COA may indicate some testing is outside the lab’s accreditation scope.",
            recommendation="Confirm which analytes are covered under accreditation for your use case.",
            evidence=ev_iso
        ))

    completed_raw = fields.get("completed_date", "")
    completed_dt = safe_parse_date(completed_raw) if completed_raw else None
    if freshness_days > 0:
        if completed_raw and completed_dt:
            age = (date.today() - completed_dt).days
            if age > freshness_days:
                findings.append(Finding(
                    severity="WARN",
                    rule_id=f"{state}-DATE-001",
                    title="COA may be older than the configured threshold",
                    meaning="Older COAs may not represent the current lot or may be less reliable for time-sensitive claims.",
                    recommendation="Request a more recent COA or document why this one is acceptable.",
                    evidence=Evidence(page_index=None, snippet=f"Completed/Released: {completed_raw} (~{age} days old). Threshold: {freshness_days} days.")
                ))
        else:
            findings.append(Finding(
                severity="INFO",
                rule_id=f"{state}-DATE-INFO",
                title="Completed/Released date not confidently extracted",
                meaning="The date may exist on the COA, but it wasn’t reliably detected in extracted text.",
                recommendation="Verify the completed/released date manually.",
                evidence=Evidence(page_index=None, snippet="No completed/released date reliably extracted.")
            ))

    if product_type in OIL_PRODUCT_TYPES:
        d8 = cannabinoids_pct.get("Δ8-THC")
        d9 = cannabinoids_pct.get("Δ9-THC")
        if d8 is not None and d9 is not None:
            if d9 >= d9_present_threshold_pct and d8 >= d8_high_threshold_pct:
                findings.append(Finding(
                    severity="WARN",
                    rule_id=f"{state}-D8D9-001",
                    title="Oil product: elevated Δ8-THC while Δ9-THC is also present",
                    meaning="This cannabinoid pattern may warrant review depending on product claims and stakeholder standards.",
                    recommendation="Confirm units, formulation intent, and whether labeling/disclosure expectations are met.",
                    evidence=Evidence(page_index=None, snippet=f"Extracted: Δ8-THC {d8:.2f}%, Δ9-THC {d9:.2f}% (thresholds: Δ8≥{d8_high_threshold_pct}%, Δ9≥{d9_present_threshold_pct}%).")
                ))
        else:
            findings.append(Finding(
                severity="INFO",
                rule_id=f"{state}-D8D9-INFO",
                title="Δ8/Δ9 cross-check limited",
                meaning="Δ8-THC and/or Δ9-THC % values were not reliably extracted.",
                recommendation="Verify Δ8 and Δ9 rows manually on the COA cannabinoid table.",
                evidence=Evidence(page_index=None, snippet="Δ8-THC and/or Δ9-THC not reliably extracted.")
            ))

    return findings

# ============================
# PDF EXPORT (READABLE)
# ============================
def wrap_text(c: canvas.Canvas, text: str, x: float, y: float, max_width: float, size=10, leading=12) -> float:
    c.setFont("Helvetica", size)
    words = (text or "").split()
    line = ""
    for w in words:
        test = (line + " " + w).strip()
        if c.stringWidth(test, "Helvetica", size) <= max_width:
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
    reviewer: str,
    source_filename: str,
    source_sha256: str,
    fields: Dict[str, str],
    panels_detected: Dict[str, bool],
    clean_panels: List[str],
    findings: List[Finding],
    can_buckets: Dict[str, List[Tuple[str, float]]],
    terp_buckets: Dict[str, List[Tuple[str, float]]],
) -> bytes:
    buf = io.BytesIO()
    c = canvas.Canvas(buf, pagesize=letter)
    width, height = letter
    margin = 0.75 * inch
    x = margin
    y = height - margin
    max_w = width - 2 * margin

    status = overall_status(findings)
    created_utc = utc_now_iso()

    c.setFont("Helvetica-Bold", 18)
    c.drawString(x, y, f"{APP_NAME} — COA Summary Report")
    y -= 22

    c.setFont("Helvetica", 10)
    c.drawString(x, y, f"Record ID: {record_id}")
    y -= 12
    c.drawString(x, y, f"Generated (UTC): {created_utc}")
    y -= 12
    c.drawString(x, y, f"Reviewer: {reviewer or 'Not provided'}")
    y -= 12
    c.drawString(x, y, f"Jurisdiction: {state}   |   Product Type: {product_type}")
    y -= 12
    c.drawString(x, y, f"Ruleset: {ruleset_version}   |   App: {APP_VERSION}")
    y -= 16

    c.setFont("Helvetica-Bold", 14)
    c.drawString(x, y, f"Overall Result: {status}")
    y -= 16

    c.setFont("Helvetica-Bold", 11)
    c.drawString(x, y, "Source File Integrity")
    y -= 14
    c.setFont("Helvetica", 10)
    y = wrap_text(c, f"Filename: {source_filename}", x, y, max_w)
    y = wrap_text(c, f"SHA-256: {source_sha256}", x, y, max_w)
    y -= 6

    c.setFont("Helvetica-Bold", 11)
    c.drawString(x, y, "Key Identifiers (as extracted)")
    y -= 14
    c.setFont("Helvetica", 10)
    keys = [
        ("Lab", fields.get("lab_name", "Not detected")),
        ("Sample ID", fields.get("sample_id", "Not detected")),
        ("Batch/Lot", fields.get("batch_id", "Not detected")),
        ("Matrix / Type", fields.get("matrix", "Not detected")),
        ("Collected", fields.get("collected_date", "Not detected")),
        ("Received", fields.get("received_date", "Not detected")),
        ("Completed/Released", fields.get("completed_date", "Not detected")),
        ("Total THC", fields.get("total_thc", "Not detected")),
        ("Total CBD", fields.get("total_cbd", "Not detected")),
        ("Total Cannabinoids", fields.get("total_cannabinoids", "Not detected")),
    ]
    for k, v in keys:
        y = wrap_text(c, f"{k}: {v}", x, y, max_w)
    y -= 8

    c.setFont("Helvetica-Bold", 11)
    c.drawString(x, y, "Plain-English Profile")
    y -= 14
    c.setFont("Helvetica", 10)

    def fmt_bucket(title: str, items: List[Tuple[str, float]]) -> str:
        if not items:
            return f"{title}: None extracted"
        return f"{title}: " + ", ".join([f"{n} ({v:.2f}%)" for n, v in items[:6]])

    y = wrap_text(c, fmt_bucket("Dominant cannabinoids", can_buckets.get("Dominant", [])), x, y, max_w)
    y = wrap_text(c, fmt_bucket("Secondary cannabinoids", can_buckets.get("Secondary", [])), x, y, max_w)
    y = wrap_text(c, fmt_bucket("Minor cannabinoids", can_buckets.get("Minor", [])), x, y, max_w)
    y -= 6
    y = wrap_text(c, fmt_bucket("Dominant terpenes", terp_buckets.get("Dominant", [])), x, y, max_w)
    y = wrap_text(c, fmt_bucket("Secondary terpenes", terp_buckets.get("Secondary", [])), x, y, max_w)
    y = wrap_text(c, fmt_bucket("Minor terpenes", terp_buckets.get("Minor", [])), x, y, max_w)
    y -= 10

    c.setFont("Helvetica-Bold", 11)
    c.drawString(x, y, "Panels — Detected in text")
    y -= 14
    c.setFont("Helvetica", 10)

    required = REQUIRED_PANELS.get(state, {}).get(product_type, [])
    optional = OPTIONAL_PANELS_BY_STATE.get(state, [])
    for p in required:
        mark = "Yes" if panels_detected.get(p, False) else "No"
        y = wrap_text(c, f"{p} (Required): {mark}", x, y, max_w)
    for p in optional:
        mark = "Yes" if panels_detected.get(p, False) else "No"
        y = wrap_text(c, f"{p} (Optional): {mark}", x, y, max_w)
    y -= 8

    if clean_panels:
        c.setFont("Helvetica-Bold", 11)
        c.drawString(x, y, "Clean Panel Notes (ND/Not Detected found)")
        y -= 14
        c.setFont("Helvetica", 10)
        y = wrap_text(c, "Leafline treats ND as favorable for contaminant-style panels (below detection).", x, y, max_w)
        for p in clean_panels:
            y = wrap_text(c, f"- {p}: ND/Not Detected language found", x, y, max_w)
        y -= 8

    c.showPage()
    y = height - margin

    c.setFont("Helvetica-Bold", 14)
    c.drawString(x, y, "Issues & Recommendations")
    y -= 18

    if not findings:
        c.setFont("Helvetica", 11)
        c.drawString(x, y, "No issues generated by the current rule set.")
        y -= 14
    else:
        for sev in ["HOLD", "WARN", "INFO"]:
            items = [f for f in findings if f.severity == sev]
            if not items:
                continue
            c.setFont("Helvetica-Bold", 12)
            c.drawString(x, y, f"{sev} ({len(items)})")
            y -= 16
            for fnd in items:
                if y < 1.2 * inch:
                    c.showPage()
                    y = height - margin
                c.setFont("Helvetica-Bold", 10)
                y = wrap_text(c, f"{fnd.rule_id} — {fnd.title}", x, y, max_w, size=10, leading=12)
                c.setFont("Helvetica", 10)
                y = wrap_text(c, f"What it means: {fnd.meaning}", x, y, max_w, size=10, leading=12)
                y = wrap_text(c, f"Recommendation: {fnd.recommendation}", x, y, max_w, size=10, leading=12)
                pg = "N/A" if fnd.evidence.page_index is None else str(fnd.evidence.page_index + 1)
                y = wrap_text(c, f"Evidence (page {pg}): {fnd.evidence.snippet}", x, y, max_w, size=9, leading=11)
                y -= 8

    c.save()
    return buf.getvalue()

# ============================
# STREAMLIT UI
# ============================
st.set_page_config(page_title="Leafline — COA Analyzer", layout="wide")
init_db()

st.title("Leafline")
st.caption("COA analysis that reads like a summary, not a spreadsheet.")

with st.sidebar:
    st.subheader("Settings")
    state = st.selectbox("Jurisdiction", STATE_OPTIONS, index=0)
    product_type = st.selectbox("Product type", PRODUCT_TYPES, index=0)
    freshness_days = st.number_input("Freshness threshold (days)", min_value=0, max_value=3650, value=365, step=30)

    st.markdown("**Δ8/Δ9 check (oil types)**")
    d8_high_threshold_pct = st.number_input("Δ8 high threshold (%)", min_value=0.0, max_value=100.0, value=5.0, step=0.5)
    d9_present_threshold_pct = st.number_input("Δ9 present threshold (%)", min_value=0.0, max_value=100.0, value=0.5, step=0.1)

    reviewer = st.text_input("Reviewer (optional)", value="")

uploaded = st.file_uploader("Upload COA (PDF, PNG, JPG)", type=["pdf", "png", "jpg", "jpeg"])

if not uploaded:
    st.info("Upload a COA to generate a plain-English summary and exportable PDF.")
    st.stop()

file_bytes = uploaded.read()
source_sha = sha256_bytes(file_bytes)
record_id = str(uuid.uuid4())
ruleset_version = f"{state}_v1.0_{datetime.now().strftime('%Y-%m-%d')}"
created_at = utc_now_iso()

is_pdf = uploaded.name.lower().endswith(".pdf")

with st.spinner("Reading document..."):
    if is_pdf:
        extracted_text, per_page_text = extract_text_from_pdf(file_bytes)
        parsing_method = "PDF text extraction"

        if len(re.sub(r"\s+", "", extracted_text)) < 400:
            try:
                with pdfplumber.open(io.BytesIO(file_bytes)) as pdf:
                    page0 = pdf.pages[0]
                    pil = page0.to_image(resolution=200).original
                    ocr_txt = pytesseract.image_to_string(pil)
                if len(re.sub(r"\s+", "", ocr_txt)) > len(re.sub(r"\s+", "", extracted_text)):
                    extracted_text = ocr_txt
                    per_page_text = [ocr_txt]
                    parsing_method = "OCR (PDF page 1 fallback)"
            except Exception:
                pass
    else:
        extracted_text = ocr_image(file_bytes)
        per_page_text = [extracted_text]
        parsing_method = "OCR (image)"

db_insert_record({
    "record_id": record_id,
    "created_at_utc": created_at,
    "reviewer": reviewer or None,
    "source_filename": uploaded.name,
    "source_sha256": source_sha,
    "source_size_bytes": len(file_bytes),
    "state": state,
    "product_type": product_type,
    "ruleset_version": ruleset_version,
    "parsing_method": parsing_method,
    "notes": None,
})
db_insert_event(record_id, "INGESTED", {
    "filename": uploaded.name,
    "sha256": source_sha,
    "state": state,
    "product_type": product_type,
    "ruleset_version": ruleset_version,
    "parsing_method": parsing_method,
    "app_version": APP_VERSION,
})

fields = extract_fields(extracted_text)
panels_detected = detect_panels(extracted_text)

# ---- TABLE-FIRST extraction (preferred) ----
table_sections = {}
if is_pdf:
    try:
        table_sections = extract_percent_tables_from_pdf(file_bytes)
    except Exception:
        table_sections = {}

cannabinoids_pct = table_sections.get("Cannabinoids", {})
terpenes_pct = table_sections.get("Terpenes", {})

# ---- FALLBACK to line scan only if tables came up empty ----
if not cannabinoids_pct:
    cannabinoids_pct = parse_compounds_by_percent(per_page_text, CANNABINOID_ALIASES)
if not terpenes_pct:
    terpenes_pct = parse_compounds_by_percent(per_page_text, TERPENE_ALIASES)

can_ranked = rank_profile(cannabinoids_pct)
terp_ranked = rank_profile(terpenes_pct)
can_buckets = bucket_cannabinoids(can_ranked)
terp_buckets = bucket_terpenes(terp_ranked)

findings = build_findings(
    state=state,
    product_type=product_type,
    fields=fields,
    panels_detected=panels_detected,
    per_page_text=per_page_text,
    freshness_days=int(freshness_days),
    d8_high_threshold_pct=float(d8_high_threshold_pct),
    d9_present_threshold_pct=float(d9_present_threshold_pct),
    cannabinoids_pct=cannabinoids_pct,
)

status = overall_status(findings)
holds = [f for f in findings if f.severity == "HOLD"]
warns = [f for f in findings if f.severity == "WARN"]
infos = [f for f in findings if f.severity == "INFO"]

clean_panels = []
for p in sorted(CONTAMINANT_PANELS):
    if panels_detected.get(p, False) and panel_has_nd(per_page_text, p):
        clean_panels.append(p)

# ============================
# FRIENDLY DASHBOARD HEADER
# ============================
top1, top2, top3, top4, top5 = st.columns([1.2, 1, 1, 1, 2])
top1.metric("Overall", status)
top2.metric("HOLD", len(holds))
top3.metric("WARN", len(warns))
top4.metric("INFO", len(infos))
top5.write(f"**Record ID:** `{record_id}`\n\n**File SHA-256:** `{source_sha[:16]}…`")

st.divider()

tab_summary, tab_findings, tab_evidence, tab_export = st.tabs(["Summary", "Findings", "Evidence", "Export"])

with tab_summary:
    left, right = st.columns([1.1, 0.9])

    with left:
        st.subheader("Plain-English Profile")

        def render_bucket(title: str, items: List[Tuple[str, float]]):
            if not items:
                st.write(f"**{title}:** None extracted")
                return
            st.write(f"**{title}:**")
            st.table([{"Compound": n, "Percent (%)": round(v, 2)} for n, v in items[:8]])

        st.markdown("### Cannabinoids")
        render_bucket("Dominant", can_buckets.get("Dominant", []))
        render_bucket("Secondary", can_buckets.get("Secondary", []))
        render_bucket("Minor", can_buckets.get("Minor", []))

        st.markdown("### Terpenes")
        render_bucket("Dominant", terp_buckets.get("Dominant", []))
        render_bucket("Secondary", terp_buckets.get("Secondary", []))
        render_bucket("Minor", terp_buckets.get("Minor", []))

    with right:
        st.subheader("Key Details")
        st.write(f"**Jurisdiction:** {state}")
        st.write(f"**Product type:** {product_type}")
        st.write(f"**Parsing method:** {parsing_method}")
        st.write("")
        st.write("**Identifiers (as extracted):**")
        st.json({
            "lab": fields.get("lab_name", "Not detected"),
            "sample_id": fields.get("sample_id", "Not detected"),
            "batch_id": fields.get("batch_id", "Not detected"),
            "matrix": fields.get("matrix", "Not detected"),
            "collected_date": fields.get("collected_date", "Not detected"),
            "received_date": fields.get("received_date", "Not detected"),
            "completed_date": fields.get("completed_date", "Not detected"),
            "total_thc": fields.get("total_thc", "Not detected"),
            "total_cbd": fields.get("total_cbd", "Not detected"),
            "total_cannabinoids": fields.get("total_cannabinoids", "Not detected"),
        })

        st.write("")
        st.subheader("Clean Panels (ND is favorable)")
        if clean_panels:
            st.success("ND/Not Detected language found for: " + ", ".join(clean_panels))
        else:
            st.info("No ND/Not Detected panel note detected (does not automatically mean failure).")

        st.write("")
        st.subheader("Panel Checklist")
        required = REQUIRED_PANELS.get(state, {}).get(product_type, [])
        optional = OPTIONAL_PANELS_BY_STATE.get(state, [])
        rows = []
        for p in required:
            rows.append({"Panel": p, "Rule": "Required", "Detected": "Yes" if panels_detected.get(p, False) else "No"})
        for p in optional:
            rows.append({"Panel": p, "Rule": "Optional", "Detected": "Yes" if panels_detected.get(p, False) else "No"})
        st.table(rows)

with tab_findings:
    st.subheader("Issues & Recommendations")
    if not findings:
        st.success("No issues generated by the current rule set.")
    else:
        for sev, items in [("HOLD", holds), ("WARN", warns), ("INFO", infos)]:
            if not items:
                continue
            with st.expander(f"{sev} ({len(items)})", expanded=(sev in ("HOLD", "WARN"))):
                for f in items:
                    pg = "N/A" if f.evidence.page_index is None else str(f.evidence.page_index + 1)
                    st.markdown(f"**{f.rule_id} — {f.title}**")
                    st.write(f"**What it means:** {f.meaning}")
                    st.write(f"**Recommendation:** {f.recommendation}")
                    st.write(f"**Evidence (page {pg}):** {f.evidence.snippet}")
                    st.divider()

with tab_evidence:
    st.subheader("Evidence Snippets (what Leafline matched)")
    st.caption("Stable view: page references + extracted snippets.")
    if not findings:
        st.write("No evidence to show.")
    else:
        for f in findings:
            pg = "N/A" if f.evidence.page_index is None else str(f.evidence.page_index + 1)
            st.write(f"**{f.severity}** — {f.title}  (page {pg})")
            st.code(f.evidence.snippet or "", language="text")

    with st.expander("Raw extracted text (debug)", expanded=False):
        st.text((extracted_text or "")[:25000])

with tab_export:
    st.subheader("Export")
    st.write("Review Summary + Findings. When ready, export a clean report.")

    if st.button("Generate PDF report", type="primary"):
        pdf_bytes = generate_pdf_report(
            record_id=record_id,
            state=state,
            product_type=product_type,
            ruleset_version=ruleset_version,
            reviewer=reviewer,
            source_filename=uploaded.name,
            source_sha256=source_sha,
            fields=fields,
            panels_detected=panels_detected,
            clean_panels=clean_panels,
            findings=findings,
            can_buckets=can_buckets,
            terp_buckets=terp_buckets,
        )
        report_sha = sha256_bytes(pdf_bytes)
        db_insert_event(record_id, "REPORT_GENERATED", {
            "report_sha256": report_sha,
            "overall_status": status,
            "finding_count": len(findings),
            "ruleset_version": ruleset_version,
            "app_version": APP_VERSION,
        })

        st.success(f"Report generated. SHA-256: {report_sha}")
        st.download_button(
            "Download PDF Report",
            data=pdf_bytes,
            file_name=f"Leafline_Report_{state}_{product_type}_{record_id}.pdf",
            mime="application/pdf",
        )
