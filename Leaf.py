import io
import re
import json
import uuid
import zipfile
import hashlib
import sqlite3
from datetime import datetime, date, timezone
from typing import List, Dict, Optional, Tuple, Any

import streamlit as st
import pandas as pd
import pdfplumber
from dateutil import parser as dateparser

# OCR fallback (no poppler needed)
from PIL import Image
import pypdfium2 as pdfium
import pytesseract

# PDF report export
from reportlab.lib.pagesizes import letter
from reportlab.lib.units import inch
from reportlab.pdfgen import canvas

# ============================
# Leafline — Batch COA Scanner
# ============================
APP_NAME = "Leafline"
APP_VERSION = "2.4.0"
DB_PATH = "leafline_audit.db"
SUPPORTED_EXTS = (".pdf",)

# ============================
# Client-required flag logic
# ============================
EXPIRY_CUTOFF = date(2021, 11, 24)
EARLY_YEAR_CUTOFF = 2020
CLIENT_THC_THRESHOLD = 0.3  # percent

DELTA8_TERMS = [r"delta\s*[-]?\s*8", r"\bdelta8\b", r"Δ\s*8", r"\bΔ8\b", r"\bD8\b", r"\b8\s*THC\b"]
DELTA9_TERMS = [r"delta\s*[-]?\s*9", r"\bdelta9\b", r"Δ\s*9", r"\bΔ9\b", r"\bD9\b", r"\b9\s*THC\b"]

THC_CONTEXT_TERMS = [r"\bTHC\b", r"tetrahydrocannabinol", r"\bcannabinoid\b", r"\bpotency\b"]

PCT_RE = re.compile(r"(\d+(?:\.\d+)?)\s*%")

RULESET_VERSION = "client_flag_v2"
FED_RULESET_VERSION = "federal_hemp_v1"

# ============================
# Federal hemp thresholds
# ============================
HEMP_DELTA9_LIMIT = 0.3   # delta-9 THC (dry weight) limit
HEMP_TOTAL_LIMIT = 0.3    # total THC (delta-9 + THCA*0.877) limit
HEMP_TOTAL_NEGLIGENT_CUTOFF = 1.0  # severity bucket
THCA_DECARB_FACTOR = 0.877


# ============================
# Utilities / Audit DB
# ============================
def utc_now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")

def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()

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

        ruleset_version TEXT NOT NULL,
        fed_ruleset_version TEXT NOT NULL,
        app_version TEXT NOT NULL,

        parsing_method TEXT NOT NULL,
        max_pages_scanned INTEGER NOT NULL,
        ocr_used INTEGER NOT NULL,

        flagged INTEGER NOT NULL,
        reasons TEXT,
        expiration_date TEXT,
        earliest_date_found TEXT,
        expired_before_cutoff INTEGER NOT NULL,
        has_early_date INTEGER NOT NULL,

        hemp_flag INTEGER NOT NULL,
        hemp_severity TEXT,
        hemp_reasons TEXT,
        hemp_delta9_pct REAL,
        hemp_thca_pct REAL,
        hemp_total_thc_pct REAL
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

def db_insert_record(row: dict):
    conn = sqlite3.connect(DB_PATH)
    cur = conn.cursor()
    cur.execute("""
    INSERT INTO records (
        record_id, created_at_utc, reviewer, source_filename, source_sha256, source_size_bytes,
        ruleset_version, fed_ruleset_version, app_version,
        parsing_method, max_pages_scanned, ocr_used,
        flagged, reasons, expiration_date, earliest_date_found, expired_before_cutoff, has_early_date,
        hemp_flag, hemp_severity, hemp_reasons, hemp_delta9_pct, hemp_thca_pct, hemp_total_thc_pct
    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    """, (
        row["record_id"], row["created_at_utc"], row.get("reviewer"),
        row["source_filename"], row["source_sha256"], row["source_size_bytes"],
        row["ruleset_version"], row["fed_ruleset_version"], row["app_version"],
        row["parsing_method"], row["max_pages_scanned"], int(row["ocr_used"]),
        int(row["flagged"]), row.get("reasons"),
        row.get("expiration_date"), row.get("earliest_date_found"),
        int(row.get("expired_before_cutoff", False)),
        int(row.get("has_early_date", False)),
        int(row["hemp_flag"]), row.get("hemp_severity"), row.get("hemp_reasons"),
        row.get("hemp_delta9_pct"), row.get("hemp_thca_pct"), row.get("hemp_total_thc_pct")
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
# Parsing helpers
# ============================
def safe_parse_date(s: str) -> Optional[date]:
    try:
        d = dateparser.parse(s, dayfirst=False, yearfirst=False, fuzzy=True)
        return d.date() if d else None
    except Exception:
        return None

def any_term(text: str, patterns: List[str]) -> bool:
    if not text:
        return False
    return any(re.search(p, text, flags=re.IGNORECASE) for p in patterns)

def extract_all_dates(text: str) -> List[date]:
    if not text:
        return []
    candidates = set()

    for m in re.finditer(r"\b(\d{1,2}[/-]\d{1,2}[/-]\d{2,4})\b", text):
        candidates.add(m.group(1))
    for m in re.finditer(r"\b(\d{4}-\d{2}-\d{2})\b", text):
        candidates.add(m.group(1))

    out = []
    for s in candidates:
        d = safe_parse_date(s)
        if d:
            out.append(d)
    return sorted(set(out))

def extract_expiration_date(text: str) -> Optional[date]:
    if not text:
        return None
    exp_line_patterns = [
        r"(?:expiration\s*date|exp\s*date|expires?|expir\w*)\s*[:\-]?\s*(\d{1,2}[/-]\d{1,2}[/-]\d{2,4})",
        r"(?:expiration\s*date|exp\s*date|expires?|expir\w*)\s*[:\-]?\s*(\d{4}-\d{2}-\d{2})",
    ]
    for pat in exp_line_patterns:
        m = re.search(pat, text, flags=re.IGNORECASE)
        if m:
            d = safe_parse_date(m.group(1))
            if d:
                return d
    return None

def extract_text_pdfplumber(pdf_bytes: bytes, max_pages: int = 6) -> str:
    per_page = []
    with pdfplumber.open(io.BytesIO(pdf_bytes)) as pdf:
        for p in pdf.pages[:max_pages]:
            per_page.append(p.extract_text() or "")
    return "\n\n".join(per_page).strip()

def render_pdf_pages_with_pdfium(pdf_bytes: bytes, max_pages: int = 6, scale: float = 2.2) -> List[Image.Image]:
    images: List[Image.Image] = []
    pdf = pdfium.PdfDocument(pdf_bytes)
    n = min(len(pdf), max_pages)
    for i in range(n):
        page = pdf[i]
        pil_img = page.render(scale=scale).to_pil()
        images.append(pil_img)
    return images

def ocr_images(images: List[Image.Image]) -> str:
    out = []
    for img in images:
        gray = img.convert("L")
        text = pytesseract.image_to_string(gray, config="--psm 6")
        out.append(text)
    return "\n\n".join(out).strip()

def extract_text_hybrid(pdf_bytes: bytes, max_pages: int, min_text_len: int, ocr_scale: float) -> Tuple[str, str, bool]:
    """
    Returns (text, method_label, ocr_used)
    """
    text = extract_text_pdfplumber(pdf_bytes, max_pages=max_pages)
    if len(text) >= min_text_len:
        return text, "pdf_text", False

    images = render_pdf_pages_with_pdfium(pdf_bytes, max_pages=max_pages, scale=ocr_scale)
    ocr_text = ocr_images(images)
    combined = (text + "\n\n" + ocr_text).strip()
    return combined, "hybrid_text+ocr", True

def text_has_thc_over_threshold(text: str, threshold: float) -> Tuple[bool, List[str]]:
    """
    Finds any % value > threshold that appears near THC/Δ8/Δ9 language.
    Returns (found, evidence_snippets)
    """
    evid = []
    if not text:
        return False, evid

    for m in re.finditer(PCT_RE, text):
        try:
            val = float(m.group(1))
        except Exception:
            continue
        if val <= threshold:
            continue

        start = max(m.start() - 80, 0)
        end = min(m.end() + 80, len(text))
        window = text[start:end]

        if re.search(r"\bTHC\b|tetrahydrocannabinol|Δ\s*8|Δ\s*9|delta\s*[-]?\s*[89]|\bD[89]\b", window, re.IGNORECASE):
            snippet = re.sub(r"\s+", " ", window).strip()
            evid.append(f"{val:.3f}% near: {snippet[:180]}")

    return (len(evid) > 0), evid


# ============================
# Federal hemp extraction
# ============================
def _find_pct_after_label(text: str, labels: List[str]) -> Optional[float]:
    if not text:
        return None
    for lab in labels:
        pat = rf"{lab}\s*[:\-]?\s*(\d+(?:\.\d+)?)\s*%"
        m = re.search(pat, text, flags=re.IGNORECASE)
        if m:
            try:
                return float(m.group(1))
            except Exception:
                pass

        pat2 = rf"{lab}.*?(\d+(?:\.\d+)?)\s*%"
        m2 = re.search(pat2, text, flags=re.IGNORECASE | re.DOTALL)
        if m2:
            try:
                return float(m2.group(1))
            except Exception:
                pass
    return None

def extract_hemp_numbers(text: str) -> Dict[str, Optional[float]]:
    delta9_labels = [
        r"Δ\s*9\s*[-]?\s*THC", r"delta\s*[-]?\s*9\s*[-]?\s*THC", r"\bd9[-\s]*thc\b",
        r"delta\s*[-]?\s*9", r"\bdelta9\b", r"\bΔ9\b"
    ]
    thca_labels = [
        r"\bTHCA\b", r"THC[-\s]*A", r"THC\s*A"
    ]
    total_thc_labels = [
        r"total\s*THC", r"Total\s*THC", r"TotalTHC"
    ]

    delta9 = _find_pct_after_label(text, delta9_labels)
    thca = _find_pct_after_label(text, thca_labels)
    total_thc = _find_pct_after_label(text, total_thc_labels)

    if total_thc is None and (delta9 is not None or thca is not None):
        d9 = delta9 or 0.0
        a = thca or 0.0
        total_thc = d9 + (a * THCA_DECARB_FACTOR)

    return {"delta9_pct": delta9, "thca_pct": thca, "total_thc_pct": total_thc}

def evaluate_federal_hemp(text: str,
                          delta9_limit: float,
                          total_limit: float,
                          negligent_cutoff: float) -> Tuple[bool, Dict[str, Any]]:
    nums = extract_hemp_numbers(text)
    d9 = nums["delta9_pct"]
    thca = nums["thca_pct"]
    total = nums["total_thc_pct"]

    reasons: List[str] = []
    severity = "none"

    if d9 is not None and d9 > delta9_limit:
        reasons.append(f"Delta-9 THC exceeds {delta9_limit}% (delta-9 = {d9:.3f}%)")
        severity = "breach"

    if total is not None and total > total_limit:
        reasons.append(f"Total THC exceeds {total_limit}% (total = {total:.3f}%)")
        severity = "breach"

    if total is not None and total > negligent_cutoff:
        reasons.append(f"Total THC exceeds {negligent_cutoff}% (total = {total:.3f}%)")
        severity = "elevated"

    if d9 is None and total is None:
        reasons.append("No reliable Delta-9/Total THC % found for federal hemp check (extraction limitation)")
        severity = "unknown"

    hemp_flag = severity in ("breach", "elevated")

    payload = {
        "reasons": reasons,
        "severity": severity,
        "delta9_pct": d9,
        "thca_pct": thca,
        "total_thc_pct": total,
    }
    return hemp_flag, payload


# ============================
# Client flag evaluation (UPDATED)
# Must flag:
# (Delta8 OR Delta9) AND (THC > 0.3) AND (Expired before 11/24/2021 OR date <= 2020)
# ============================
def evaluate_client_flag(text: str) -> Tuple[bool, Dict[str, Any]]:
    reasons: List[str] = []

    has_delta = any_term(text, DELTA8_TERMS) or any_term(text, DELTA9_TERMS)
    has_thc_context = any_term(text, THC_CONTEXT_TERMS)

    thc_over, thc_evidence = text_has_thc_over_threshold(text, CLIENT_THC_THRESHOLD)

    exp_date = extract_expiration_date(text)
    all_dates = extract_all_dates(text)
    early_dates = [d for d in all_dates if d.year <= EARLY_YEAR_CUTOFF]

    expired_before_cutoff = bool(exp_date and exp_date < EXPIRY_CUTOFF)
    has_early_date = bool(early_dates)

    # Friendly reasons
    if has_delta:
        reasons.append("Delta 8/9 term detected")
    else:
        reasons.append("No Delta 8/9 term detected")

    if has_thc_context:
        reasons.append("THC/cannabinoid context detected")
    else:
        reasons.append("No THC/cannabinoid context detected")

    if thc_over:
        reasons.append(f"THC level above {CLIENT_THC_THRESHOLD}% detected")
    else:
        reasons.append(f"No THC level above {CLIENT_THC_THRESHOLD}% detected")

    if exp_date:
        reasons.append(f"Expiration date found: {exp_date.isoformat()}")
    else:
        reasons.append("No expiration date found")

    if expired_before_cutoff:
        reasons.append(f"Expired before {EXPIRY_CUTOFF.isoformat()}")

    if has_early_date:
        reasons.append(f"Contains date(s) in {EARLY_YEAR_CUTOFF} or earlier (e.g., {early_dates[0].isoformat()})")

    # FINAL required logic
    date_condition = expired_before_cutoff or has_early_date
    flagged = bool(has_delta and has_thc_context and thc_over and date_condition)

    if not date_condition:
        reasons.append(
            f"Date condition not met (needs expired before {EXPIRY_CUTOFF.isoformat()} OR a date in {EARLY_YEAR_CUTOFF} or earlier)"
        )

    details = {
        "expiration_date": exp_date.isoformat() if exp_date else "",
        "earliest_date_found": (
            early_dates[0].isoformat() if early_dates else (all_dates[0].isoformat() if all_dates else "")
        ),
        "expired_before_cutoff": expired_before_cutoff,
        "has_early_date": has_early_date,
        "thc_evidence": thc_evidence,
    }

    return flagged, {"reasons": reasons, "details": details}


# ============================
# PDF batch report generator
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

def generate_batch_pdf_report(rows: List[Dict[str, Any]]) -> bytes:
    buf = io.BytesIO()
    c = canvas.Canvas(buf, pagesize=letter)
    width, height = letter
    margin = 0.75 * inch
    x = margin
    y = height - margin
    max_w = width - 2 * margin

    total = len(rows)
    client_flagged = sum(1 for r in rows if r.get("flagged") is True)
    hemp_flagged = sum(1 for r in rows if r.get("hemp_flag") is True)
    created = utc_now_iso()

    c.setFont("Helvetica-Bold", 18)
    c.drawString(x, y, f"{APP_NAME} — Batch Report")
    y -= 22

    c.setFont("Helvetica", 10)
    c.drawString(x, y, f"Generated (UTC): {created}")
    y -= 12
    c.drawString(x, y, f"App: {APP_VERSION}   |   Rulesets: {RULESET_VERSION} / {FED_RULESET_VERSION}")
    y -= 12
    c.drawString(x, y, f"Total PDFs scanned: {total}   |   Flagged: {client_flagged}   |   Hemp-flagged: {hemp_flagged}")
    y -= 16

    c.setFont("Helvetica-Bold", 11)
    c.drawString(x, y, "Client Flag Logic")
    y -= 14
    c.setFont("Helvetica", 10)
    y = wrap_text(
        c,
        f"Flag if: (Delta 8 or Delta 9) AND (THC > {CLIENT_THC_THRESHOLD}%) AND (Expired before {EXPIRY_CUTOFF.isoformat()} OR date in {EARLY_YEAR_CUTOFF} or earlier).",
        x, y, max_w
    )
    y -= 8

    c.setFont("Helvetica-Bold", 11)
    c.drawString(x, y, "Federal Hemp Checks")
    y -= 14
    c.setFont("Helvetica", 10)
    y = wrap_text(
        c,
        "Hemp checks include Delta-9 THC and Total THC (Delta-9 + THCA*0.877). Severity increases if Total THC > 1.0%.",
        x, y, max_w
    )
    y -= 10

    c.setFont("Helvetica-Bold", 12)
    c.drawString(x, y, "Flagged PDFs (details)")
    y -= 16

    flagged_rows = [r for r in rows if (r.get("flagged") is True or r.get("hemp_flag") is True)]
    if not flagged_rows:
        c.setFont("Helvetica", 11)
        c.drawString(x, y, "No PDFs matched the selected flag criteria.")
        c.save()
        return buf.getvalue()

    for r in flagged_rows:
        if y < 1.2 * inch:
            c.showPage()
            y = height - margin

        c.setFont("Helvetica-Bold", 10)
        y = wrap_text(c, r["filename"], x, y, max_w, size=10, leading=12)

        c.setFont("Helvetica", 9)
        y = wrap_text(c, f"SHA-256: {r.get('sha256', '')}", x, y, max_w, size=9, leading=11)
        y = wrap_text(
            c,
            f"Extraction: {r.get('parsing_method', '')} (OCR used: {bool(r.get('ocr_used'))}, pages scanned: {r.get('max_pages_scanned')})",
            x, y, max_w, size=9, leading=11
        )

        if r.get("expiration_date"):
            y = wrap_text(c, f"Expiration date: {r['expiration_date']}", x, y, max_w, size=9, leading=11)
        if r.get("earliest_date_found"):
            y = wrap_text(c, f"Earliest date found: {r['earliest_date_found']}", x, y, max_w, size=9, leading=11)

        # Federal hemp values
        d9 = r.get("hemp_delta9_pct")
        thca = r.get("hemp_thca_pct")
        tot = r.get("hemp_total_thc_pct")
        y = wrap_text(
            c,
            f"Federal hemp values: delta-9={'' if d9 is None else f'{d9:.3f}%'}  THCA={'' if thca is None else f'{thca:.3f}%'}  total={'' if tot is None else f'{tot:.3f}%'}",
            x, y, max_w, size=9, leading=11
        )

        if r.get("thc_evidence"):
            y = wrap_text(c, "THC evidence:", x, y, max_w, size=9, leading=11)
            for ev in r["thc_evidence"][:6]:
                y = wrap_text(c, f"- {ev}", x + 12, y, max_w - 12, size=9, leading=11)

        if r.get("hemp_reasons"):
            y = wrap_text(c, f"Hemp notes: {r.get('hemp_reasons')}", x, y, max_w, size=9, leading=11)

        y = wrap_text(c, f"Client reasons: {r.get('reasons', '')}", x, y, max_w, size=9, leading=11)
        y -= 8

    c.save()
    return buf.getvalue()


# ============================
# Streamlit UI
# ============================
st.set_page_config(page_title=f"{APP_NAME} — Batch COA Scanner", layout="wide")
init_db()

st.title(APP_NAME)
st.caption("Upload a ZIP of PDFs. Leafline scans each file, flags matches, and exports a detailed batch report.")

with st.sidebar:
    st.subheader("Scan settings")
    max_pages = st.slider("Pages to scan per PDF", 1, 30, 8)
    min_text_len = st.slider("OCR trigger threshold (characters)", 50, 800, 200)
    ocr_scale = st.slider("OCR quality (higher = slower)", 1.5, 3.0, 2.2, 0.1)

    st.markdown("---")
    st.subheader("Federal hemp checks")
    enable_hemp = st.toggle("Enable federal hemp checks", value=True)
    hemp_delta9_limit = st.number_input("Delta-9 THC limit (%)", value=float(HEMP_DELTA9_LIMIT), step=0.1, format="%.3f")
    hemp_total_limit = st.number_input("Total THC limit (%)", value=float(HEMP_TOTAL_LIMIT), step=0.1, format="%.3f")
    hemp_negligent_cutoff = st.number_input("Severity threshold (%)", value=float(HEMP_TOTAL_NEGLIGENT_CUTOFF), step=0.1, format="%.3f")

    st.markdown("---")
    reviewer = st.text_input("Reviewer (optional)", value="")

zip_up = st.file_uploader("Upload ZIP of PDFs", type=["zip"])
run = st.button("Run batch scan", type="primary", disabled=(zip_up is None))

if "batch_rows" not in st.session_state:
    st.session_state["batch_rows"] = []

if zip_up and run:
    zbytes = zip_up.read()
    out_rows: List[Dict[str, Any]] = []

    prog = st.progress(0.0)
    status = st.empty()

    with zipfile.ZipFile(io.BytesIO(zbytes), "r") as z:
        names = [n for n in z.namelist() if n.lower().endswith(SUPPORTED_EXTS) and not n.endswith("/")]
        total = len(names)

        if total == 0:
            st.error("No PDFs found in the ZIP.")
        else:
            for i, name in enumerate(names, start=1):
                status.write(f"Scanning {i}/{total}: {name}")
                record_id = str(uuid.uuid4())
                created_at = utc_now_iso()

                try:
                    pdf_bytes = z.read(name)
                    sha = sha256_bytes(pdf_bytes)

                    db_insert_event(record_id, "INGESTED", {
                        "filename": name,
                        "sha256": sha,
                        "size_bytes": len(pdf_bytes),
                        "max_pages_scanned": max_pages,
                        "min_text_len": min_text_len,
                        "ocr_scale": ocr_scale,
                        "ruleset_version": RULESET_VERSION,
                        "fed_ruleset_version": FED_RULESET_VERSION,
                        "app_version": APP_VERSION,
                        "enable_hemp": enable_hemp,
                    })

                    text, method, ocr_used = extract_text_hybrid(
                        pdf_bytes,
                        max_pages=max_pages,
                        min_text_len=min_text_len,
                        ocr_scale=ocr_scale
                    )

                    # Client flag (updated)
                    flagged, payload = evaluate_client_flag(text)
                    reasons_list = payload["reasons"]
                    details = payload["details"]

                    # Federal hemp
                    hemp_flag = False
                    hemp_payload = {
                        "reasons": [],
                        "severity": "none",
                        "delta9_pct": None,
                        "thca_pct": None,
                        "total_thc_pct": None,
                    }
                    if enable_hemp:
                        hemp_flag, hemp_payload = evaluate_federal_hemp(
                            text,
                            delta9_limit=float(hemp_delta9_limit),
                            total_limit=float(hemp_total_limit),
                            negligent_cutoff=float(hemp_negligent_cutoff),
                        )

                    row = {
                        "record_id": record_id,
                        "created_at_utc": created_at,
                        "filename": name,
                        "sha256": sha,
                        "size_bytes": len(pdf_bytes),
                        "parsing_method": method,
                        "ocr_used": ocr_used,
                        "max_pages_scanned": max_pages,

                        "flagged": bool(flagged),
                        "reasons": "; ".join(reasons_list),
                        "expiration_date": details.get("expiration_date") or "",
                        "earliest_date_found": details.get("earliest_date_found") or "",
                        "expired_before_cutoff": details.get("expired_before_cutoff", False),
                        "has_early_date": details.get("has_early_date", False),
                        "thc_evidence": details.get("thc_evidence") or [],

                        "hemp_flag": bool(hemp_flag),
                        "hemp_severity": hemp_payload.get("severity", "none"),
                        "hemp_reasons": "; ".join(hemp_payload.get("reasons", [])),
                        "hemp_delta9_pct": hemp_payload.get("delta9_pct"),
                        "hemp_thca_pct": hemp_payload.get("thca_pct"),
                        "hemp_total_thc_pct": hemp_payload.get("total_thc_pct"),

                        "ruleset_version": RULESET_VERSION,
                        "fed_ruleset_version": FED_RULESET_VERSION,
                        "app_version": APP_VERSION,
                    }
                    out_rows.append(row)

                    db_insert_record({
                        "record_id": record_id,
                        "created_at_utc": created_at,
                        "reviewer": reviewer or None,
                        "source_filename": name,
                        "source_sha256": sha,
                        "source_size_bytes": len(pdf_bytes),

                        "ruleset_version": RULESET_VERSION,
                        "fed_ruleset_version": FED_RULESET_VERSION,
                        "app_version": APP_VERSION,

                        "parsing_method": method,
                        "max_pages_scanned": max_pages,
                        "ocr_used": ocr_used,

                        "flagged": bool(flagged),
                        "reasons": "; ".join(reasons_list),
                        "expiration_date": details.get("expiration_date") or None,
                        "earliest_date_found": details.get("earliest_date_found") or None,
                        "expired_before_cutoff": details.get("expired_before_cutoff", False),
                        "has_early_date": details.get("has_early_date", False),

                        "hemp_flag": bool(hemp_flag),
                        "hemp_severity": hemp_payload.get("severity", "none"),
                        "hemp_reasons": "; ".join(hemp_payload.get("reasons", [])),
                        "hemp_delta9_pct": hemp_payload.get("delta9_pct"),
                        "hemp_thca_pct": hemp_payload.get("thca_pct"),
                        "hemp_total_thc_pct": hemp_payload.get("total_thc_pct"),
                    })

                    db_insert_event(record_id, "EVALUATED", {
                        "client_flagged": bool(flagged),
                        "client_reasons": reasons_list,
                        "expiration_date": details.get("expiration_date"),
                        "earliest_date_found": details.get("earliest_date_found"),
                        "expired_before_cutoff": details.get("expired_before_cutoff", False),
                        "has_early_date": details.get("has_early_date", False),
                        "thc_evidence": (details.get("thc_evidence") or [])[:10],
                        "parsing_method": method,
                        "ocr_used": ocr_used,

                        "hemp_flag": bool(hemp_flag),
                        "hemp_severity": hemp_payload.get("severity"),
                        "hemp_reasons": hemp_payload.get("reasons", []),
                        "hemp_values": {
                            "delta9_pct": hemp_payload.get("delta9_pct"),
                            "thca_pct": hemp_payload.get("thca_pct"),
                            "total_thc_pct": hemp_payload.get("total_thc_pct"),
                        }
                    })

                except Exception as e:
                    db_insert_event(record_id, "ERROR", {
                        "filename": name,
                        "error": str(e),
                    })
                    out_rows.append({
                        "record_id": record_id,
                        "created_at_utc": created_at,
                        "filename": name,
                        "sha256": "",
                        "size_bytes": 0,
                        "parsing_method": "error",
                        "ocr_used": False,
                        "max_pages_scanned": max_pages,

                        "flagged": False,
                        "reasons": f"ERROR: {e}",
                        "expiration_date": "",
                        "earliest_date_found": "",
                        "expired_before_cutoff": False,
                        "has_early_date": False,
                        "thc_evidence": [],

                        "hemp_flag": False,
                        "hemp_severity": "none",
                        "hemp_reasons": "",
                        "hemp_delta9_pct": None,
                        "hemp_thca_pct": None,
                        "hemp_total_thc_pct": None,

                        "ruleset_version": RULESET_VERSION,
                        "fed_ruleset_version": FED_RULESET_VERSION,
                        "app_version": APP_VERSION,
                    })

                prog.progress(i / total)

    st.session_state["batch_rows"] = out_rows

rows = st.session_state.get("batch_rows", [])
if rows:
    df = pd.DataFrame([{
        "record_id": r["record_id"],
        "created_at_utc": r["created_at_utc"],
        "filename": r["filename"],

        "flagged": r["flagged"],
        "expired_before_cutoff": r.get("expired_before_cutoff", False),
        "has_early_date": r.get("has_early_date", False),
        "reasons": r["reasons"],

        "hemp_flagged": r["hemp_flag"],
        "hemp_severity": r.get("hemp_severity", ""),
        "hemp_reasons": r.get("hemp_reasons", ""),
        "hemp_delta9_pct": r.get("hemp_delta9_pct"),
        "hemp_thca_pct": r.get("hemp_thca_pct"),
        "hemp_total_thc_pct": r.get("hemp_total_thc_pct"),

        "expiration_date": r["expiration_date"],
        "earliest_date_found": r["earliest_date_found"],
        "thc_evidence": " | ".join(r.get("thc_evidence", [])[:3]),

        "sha256": r["sha256"],
        "parsing_method": r["parsing_method"],
        "ocr_used": r["ocr_used"],
        "pages_scanned": r["max_pages_scanned"],

        "ruleset_version": r["ruleset_version"],
        "fed_ruleset_version": r["fed_ruleset_version"],
        "app_version": r["app_version"],
    } for r in rows])

    total = len(df)
    client_flag_ct = int(df["flagged"].sum())
    hemp_flag_ct = int(df["hemp_flagged"].sum())
    err_ct = int((df["parsing_method"] == "error").sum())
    ocr_ct = int(df["ocr_used"].sum())

    c1, c2, c3, c4, c5 = st.columns([1, 1, 1, 1, 2])
    c1.metric("Total scanned", total)
    c2.metric("Flagged", client_flag_ct)
    c3.metric("Hemp-flagged", hemp_flag_ct)
    c4.metric("OCR used", ocr_ct)
    c5.metric("Errors", err_ct)

    st.divider()

    st.subheader("Batch results")
    st.dataframe(df, use_container_width=True)

    st.subheader("Flagged (client or hemp)")
    flagged_df = df[(df["flagged"] == True) | (df["hemp_flagged"] == True)].copy()
    if len(flagged_df) == 0:
        st.info("No PDFs matched the selected flag criteria.")
    else:
        st.dataframe(flagged_df, use_container_width=True)

    st.divider()
    st.subheader("Export")

    csv_bytes = df.to_csv(index=False).encode("utf-8")
    st.download_button(
        "Download CSV",
        data=csv_bytes,
        file_name=f"Leafline_Batch_{datetime.utcnow().strftime('%Y%m%d_%H%M%S')}Z.csv",
        mime="text/csv",
    )

    batch_pdf = generate_batch_pdf_report(rows)
    st.download_button(
        "Download Batch PDF Report",
        data=batch_pdf,
        file_name=f"Leafline_Batch_Report_{datetime.utcnow().strftime('%Y%m%d_%H%M%S')}Z.pdf",
        mime="application/pdf",
    )
else:
    st.info("Upload a ZIP of PDFs to run a batch scan.")
