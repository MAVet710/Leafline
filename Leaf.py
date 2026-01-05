import io
import re
import json
import uuid
import zipfile
import hashlib
import sqlite3
from dataclasses import dataclass
from datetime import datetime, date, timezone
from typing import List, Dict, Optional, Tuple, Any

import streamlit as st
import pandas as pd
import pdfplumber
from dateutil import parser as dateparser

# OCR fallback stack (no poppler needed)
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
APP_VERSION = "2.2.0"
DB_PATH = "leafline_audit.db"
SUPPORTED_EXTS = (".pdf",)

# ============================
# Flag criteria (client logic)
# ============================
EXPIRY_CUTOFF = date(2021, 11, 24)
EARLY_YEAR_CUTOFF = 2020
THC_THRESHOLD = 0.3  # percent

DELTA8_TERMS = [r"delta\s*[-]?\s*8", r"\bdelta8\b", r"Δ\s*8", r"\bΔ8\b", r"\bD8\b", r"\b8\s*THC\b"]
DELTA9_TERMS = [r"delta\s*[-]?\s*9", r"\bdelta9\b", r"Δ\s*9", r"\bΔ9\b", r"\bD9\b", r"\b9\s*THC\b"]

THC_CONTEXT_TERMS = [r"\bTHC\b", r"tetrahydrocannabinol", r"\bcannabinoid\b", r"\bpotency\b"]
EXPIRY_TERMS = [r"expir\w*", r"expiration\s*date", r"\bexp\s*date\b", r"\bdated\b", r"manufactur\w*", r"\bmfg\b"]

PCT_RE = re.compile(r"(\d+(?:\.\d+)?)\s*%")

RULESET_VERSION = "batch_flag_v1"

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
        app_version TEXT NOT NULL,
        parsing_method TEXT NOT NULL,
        max_pages_scanned INTEGER NOT NULL,
        ocr_used INTEGER NOT NULL,
        flagged INTEGER NOT NULL,
        reasons TEXT,
        expiration_date TEXT,
        earliest_date_found TEXT
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
        ruleset_version, app_version, parsing_method, max_pages_scanned, ocr_used,
        flagged, reasons, expiration_date, earliest_date_found
    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    """, (
        row["record_id"], row["created_at_utc"], row.get("reviewer"),
        row["source_filename"], row["source_sha256"], row["source_size_bytes"],
        row["ruleset_version"], row["app_version"], row["parsing_method"],
        row["max_pages_scanned"], int(row["ocr_used"]),
        int(row["flagged"]), row.get("reasons"),
        row.get("expiration_date"), row.get("earliest_date_found")
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

    # OCR fallback
    images = render_pdf_pages_with_pdfium(pdf_bytes, max_pages=max_pages, scale=ocr_scale)
    ocr_text = ocr_images(images)
    combined = (text + "\n\n" + ocr_text).strip()
    return combined, "hybrid_text+ocr", True

def text_has_thc_over_threshold(text: str, threshold: float) -> Tuple[bool, List[str]]:
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

        start = max(m.start() - 60, 0)
        end = min(m.end() + 60, len(text))
        window = text[start:end]

        if re.search(r"\bTHC\b|tetrahydrocannabinol|Δ\s*8|Δ\s*9|delta\s*[-]?\s*[89]|\bD[89]\b", window, re.IGNORECASE):
            snippet = re.sub(r"\s+", " ", window).strip()
            evid.append(f"{val:.3f}% near: {snippet[:160]}")

    return (len(evid) > 0), evid

# ============================
# Flag evaluation (client logic)
# ============================
def evaluate_flag(text: str) -> Tuple[bool, Dict[str, Any]]:
    reasons: List[str] = []

    has_delta = any_term(text, DELTA8_TERMS) or any_term(text, DELTA9_TERMS)
    has_thc_context = any_term(text, THC_CONTEXT_TERMS)
    has_exp_terms = any_term(text, EXPIRY_TERMS)

    exp_date = extract_expiration_date(text)
    all_dates = extract_all_dates(text)
    early_dates = [d for d in all_dates if d.year <= EARLY_YEAR_CUTOFF]

    thc_over, thc_evidence = text_has_thc_over_threshold(text, THC_THRESHOLD)

    if has_delta:
        reasons.append("Δ8/Δ9 term detected")
    if has_thc_context:
        reasons.append("THC/cannabinoid context detected")
    if has_exp_terms:
        reasons.append("Expiration/dated/manufacture language detected")

    if thc_over:
        reasons.append(f"THC-related % exceeds {THC_THRESHOLD}%")
    else:
        reasons.append(f"No THC % > {THC_THRESHOLD}% found near THC terms")

    if exp_date and exp_date < EXPIRY_CUTOFF:
        reasons.append(f"Expiration date before {EXPIRY_CUTOFF.isoformat()} ({exp_date.isoformat()})")
    if early_dates:
        reasons.append(f"Contains date(s) in {EARLY_YEAR_CUTOFF} or earlier (e.g., {early_dates[0].isoformat()})")

    # Main boolean rule:
    flagged = bool(has_delta and has_thc_context and has_exp_terms and thc_over)

    details = {
        "expiration_date": exp_date.isoformat() if exp_date else "",
        "earliest_date_found": (
            early_dates[0].isoformat() if early_dates else (all_dates[0].isoformat() if all_dates else "")
        ),
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
    flagged = sum(1 for r in rows if r.get("flagged") is True)
    created = utc_now_iso()

    c.setFont("Helvetica-Bold", 18)
    c.drawString(x, y, f"{APP_NAME} — Batch Report")
    y -= 22

    c.setFont("Helvetica", 10)
    c.drawString(x, y, f"Generated (UTC): {created}")
    y -= 12
    c.drawString(x, y, f"App: {APP_VERSION}   |   Ruleset: {RULESET_VERSION}")
    y -= 12
    c.drawString(x, y, f"Total PDFs scanned: {total}   |   Flagged: {flagged}")
    y -= 16

    c.setFont("Helvetica-Bold", 11)
    c.drawString(x, y, "Flag Logic")
    y -= 14
    c.setFont("Helvetica", 10)
    y = wrap_text(
        c,
        "Flag if: (Δ8 or Δ9) AND (THC/cannabinoid context) AND (expiration/dated/manufacture language) AND (THC-related % > 0.3%).",
        x, y, max_w
    )
    y = wrap_text(
        c,
        f"Date notes included: expiration date before {EXPIRY_CUTOFF.isoformat()} and/or any detected date in {EARLY_YEAR_CUTOFF} or earlier.",
        x, y, max_w
    )
    y -= 10

    c.setFont("Helvetica-Bold", 12)
    c.drawString(x, y, "Flagged PDFs (details)")
    y -= 16

    flagged_rows = [r for r in rows if r.get("flagged") is True]
    if not flagged_rows:
        c.setFont("Helvetica", 11)
        c.drawString(x, y, "No PDFs matched the flag criteria.")
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

        if r.get("thc_evidence"):
            y = wrap_text(c, "THC evidence:", x, y, max_w, size=9, leading=11)
            for ev in r["thc_evidence"][:6]:
                y = wrap_text(c, f"- {ev}", x + 12, y, max_w - 12, size=9, leading=11)

        y = wrap_text(c, f"Reasons: {r.get('reasons', '')}", x, y, max_w, size=9, leading=11)
        y -= 8

    c.save()
    return buf.getvalue()

# ============================
# Streamlit UI (user-friendly)
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
    reviewer = st.text_input("Reviewer (optional)", value="")
    st.markdown("---")
    st.markdown("**Flag criteria**")
    st.write("Δ8/Δ9 term + THC context + expiration/dated/manufacture + THC-related % > 0.3%")
    st.write(f"Date notes: expiration < {EXPIRY_CUTOFF.isoformat()} or any date <= {EARLY_YEAR_CUTOFF}")

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
                        "app_version": APP_VERSION,
                    })

                    text, method, ocr_used = extract_text_hybrid(
                        pdf_bytes,
                        max_pages=max_pages,
                        min_text_len=min_text_len,
                        ocr_scale=ocr_scale
                    )

                    flagged, payload = evaluate_flag(text)
                    reasons_list = payload["reasons"]
                    details = payload["details"]

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
                        "thc_evidence": details.get("thc_evidence") or [],
                        "ruleset_version": RULESET_VERSION,
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
                        "app_version": APP_VERSION,
                        "parsing_method": method,
                        "max_pages_scanned": max_pages,
                        "ocr_used": ocr_used,
                        "flagged": bool(flagged),
                        "reasons": "; ".join(reasons_list),
                        "expiration_date": details.get("expiration_date") or None,
                        "earliest_date_found": details.get("earliest_date_found") or None,
                    })

                    db_insert_event(record_id, "EVALUATED", {
                        "flagged": bool(flagged),
                        "reasons": reasons_list,
                        "expiration_date": details.get("expiration_date"),
                        "earliest_date_found": details.get("earliest_date_found"),
                        "thc_evidence": details.get("thc_evidence")[:10],
                        "parsing_method": method,
                        "ocr_used": ocr_used,
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
                        "thc_evidence": [],
                        "ruleset_version": RULESET_VERSION,
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
        "reasons": r["reasons"],
        "expiration_date": r["expiration_date"],
        "earliest_date_found": r["earliest_date_found"],
        "thc_evidence": " | ".join(r.get("thc_evidence", [])[:3]),
        "sha256": r["sha256"],
        "parsing_method": r["parsing_method"],
        "ocr_used": r["ocr_used"],
        "pages_scanned": r["max_pages_scanned"],
        "ruleset_version": r["ruleset_version"],
        "app_version": r["app_version"],
    } for r in rows])

    total = len(df)
    flagged_ct = int(df["flagged"].sum())
    err_ct = int((df["parsing_method"] == "error").sum())
    ocr_ct = int(df["ocr_used"].sum())

    c1, c2, c3, c4 = st.columns([1, 1, 1, 2])
    c1.metric("Total scanned", total)
    c2.metric("Flagged", flagged_ct)
    c3.metric("OCR used", ocr_ct)
    c4.metric("Errors", err_ct)

    st.divider()

    st.subheader("Batch results")
    st.dataframe(df, use_container_width=True)

    st.subheader("Flagged only")
    flagged_df = df[df["flagged"] == True].copy()
    if len(flagged_df) == 0:
        st.info("No PDFs matched the flag criteria.")
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
