# app.py
"""
Leafline — Batch COA Scanner (litigation-grade)

Includes:
- Percent-column extraction anchored to header "Percent" AND LOQ (prevents LOQ bleed).
- Column-window extraction for % values (fixes wrong-number pulls).
- OCR table auto-crop + dual OCR (normal + inverted), picks best.
- LOQ gating: if % < LOQ treat as ND (0.0) for hemp/threshold checks (prevents false positives).
- "Analysis Completed" treated as primary test date; effective expiration = (Analysis Completed + 365 days) if no explicit expiration.
- Batch PDF report includes an Executive Summary narrative (2 paragraphs + key findings).

Updates:
- Parallel crash fix: worker processes skip Streamlit UI execution (spawn-safe).
- ETA: live elapsed/avg/ETA shown in progress bar text when Streamlit supports it.

Run:
  streamlit run app.py
"""

import io
import os
import re
import json
import uuid
import zipfile
import hashlib
import sqlite3
import multiprocessing as mp
import time
import traceback
from dataclasses import dataclass, asdict
from datetime import datetime, date, timezone, timedelta
from collections import Counter
from typing import List, Dict, Optional, Tuple, Any, Iterable
from concurrent.futures import ProcessPoolExecutor, as_completed

import streamlit as st
import pandas as pd
import pdfplumber
from dateutil import parser as dateparser

from PIL import Image, ImageOps, ImageFilter
import pypdfium2 as pdfium
import pytesseract
from pytesseract import Output

from reportlab.lib.pagesizes import letter
from reportlab.lib.units import inch
from reportlab.pdfgen import canvas


# ============================
# App constants
# ============================
APP_NAME = "Leafline"
APP_VERSION = "3.6.4"
DB_PATH = "leafline_audit.db"
SUPPORTED_EXTS = (".pdf",)

# ============================
# Client-required flag logic
# ============================
EXPIRY_CUTOFF = date(2021, 11, 24)
EARLY_YEAR_CUTOFF = 2020
CLIENT_THC_THRESHOLD = 0.3  # percent
COA_VALIDITY_DAYS = 365  # based on Analysis Completed

DELTA8_TERMS = [
    r"delta\s*[-]?\s*8", r"\bdelta8\b", r"Δ\s*[-]?\s*8", r"\bΔ8\b", r"\bD8\b", r"\bd8[-\s]*thc\b",
    r"Δ\s*[-]?\s*8\s*thc",
]
DELTA9_TERMS = [
    r"delta\s*[-]?\s*9", r"\bdelta9\b", r"Δ\s*[-]?\s*9", r"\bΔ9\b", r"\bD9\b", r"\bd9[-\s]*thc\b",
    r"Δ\s*[-]?\s*9\s*thc",
]
THC_CONTEXT_TERMS = [r"\bTHC\b", r"tetrahydrocannabinol", r"\bcannabinoid\b", r"\bpotency\b"]

RULESET_VERSION = "client_flag_v16_len_fix_loq_anchor_split_header_ocr_fallback"
FED_RULESET_VERSION = "federal_hemp_v1"

# ============================
# Federal hemp thresholds
# ============================
HEMP_DELTA9_LIMIT = 0.3
HEMP_TOTAL_LIMIT = 0.3
HEMP_TOTAL_NEGLIGENT_CUTOFF = 1.0
THCA_DECARB_FACTOR = 0.877


# ============================
# Generic helpers
# ============================
def utc_now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _norm(s: str) -> str:
    return re.sub(r"\s+", " ", (s or "").strip()).lower()


def _norm_analyte(s: str) -> str:
    s2 = (s or "").replace("Δ", "delta")
    s2 = re.sub(r"\s+", " ", s2).strip().lower()
    return s2.replace("–", "-").replace("—", "-")


def any_term(text: str, patterns: List[str]) -> bool:
    if not text:
        return False
    return any(re.search(p, text, flags=re.IGNORECASE) for p in patterns)


def safe_parse_date(s: str) -> Optional[date]:
    try:
        d = dateparser.parse(s, dayfirst=False, yearfirst=False, fuzzy=True)
        return d.date() if d else None
    except Exception:
        return None


def _parse_float_or_nd(val: str) -> Optional[float]:
    if val is None:
        return None
    s = str(val).strip()
    if not s:
        return None
    if re.fullmatch(r"(?:nd|n\.d\.|n/d|not detected)", s, flags=re.IGNORECASE):
        return 0.0
    s = s.replace(",", "")
    m = re.search(r"(\d+(?:\.\d+)?)", s)
    if not m:
        return None
    try:
        return float(m.group(1))
    except Exception:
        return None


def _fmt_pct(v: Optional[float]) -> str:
    return "" if v is None else f"{float(v):.3f}%"


def _pct(part: int, total: int) -> str:
    if total <= 0:
        return "0.0%"
    return f"{(part / total) * 100.0:.1f}%"


def safe_pdf_page_count(pdf_bytes: bytes) -> int:
    try:
        with pdfplumber.open(io.BytesIO(pdf_bytes)) as pdf:
            return len(pdf.pages)
    except Exception:
        try:
            return len(pdfium.PdfDocument(pdf_bytes))
        except Exception:
            return 0


# ============================
# Evidence structures
# ============================
@dataclass(frozen=True)
class PotencyEvidence:
    key: str
    value_pct: Optional[float]
    source: str  # "table" | "ocr_row" | "ocr_layout" | "inline_text"
    confidence: str  # "high" | "medium" | "low" | "none" | "computed"
    page: Optional[int] = None
    raw_name: Optional[str] = None
    raw_value: Optional[str] = None
    snippet: Optional[str] = None
    notes: Optional[str] = None


@dataclass(frozen=True)
class DateEvidence:
    kind: str
    value: str
    source: str  # "regex" | "derived"
    snippet: Optional[str] = None


# ============================
# DB (main process only)
# ============================
@st.cache_resource
def get_db_conn() -> sqlite3.Connection:
    conn = sqlite3.connect(DB_PATH, check_same_thread=False)
    conn.execute("PRAGMA journal_mode=WAL;")
    return conn


def init_db():
    conn = get_db_conn()
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
        review_needed INTEGER NOT NULL,
        reasons TEXT,

        expiration_date TEXT,
        effective_expiration_date TEXT,
        test_date TEXT,
        earliest_date_found TEXT,
        expired_before_cutoff INTEGER NOT NULL,
        expired_as_of_scan INTEGER NOT NULL,
        has_early_date INTEGER NOT NULL,

        hemp_flag INTEGER NOT NULL,
        hemp_severity TEXT,
        hemp_reasons TEXT,
        hemp_delta9_pct REAL,
        hemp_thca_pct REAL,
        hemp_total_thc_pct REAL,

        potency_json TEXT,
        evidence_json TEXT,
        percent_map_count INTEGER
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


def db_insert_record(row: dict):
    conn = get_db_conn()
    cur = conn.cursor()
    cur.execute("""
    INSERT INTO records (
        record_id, created_at_utc, reviewer, source_filename, source_sha256, source_size_bytes,
        ruleset_version, fed_ruleset_version, app_version,
        parsing_method, max_pages_scanned, ocr_used,
        flagged, review_needed, reasons,

        expiration_date, effective_expiration_date, test_date, earliest_date_found,
        expired_before_cutoff, expired_as_of_scan, has_early_date,

        hemp_flag, hemp_severity, hemp_reasons, hemp_delta9_pct, hemp_thca_pct, hemp_total_thc_pct,

        potency_json, evidence_json, percent_map_count
    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
    """, (
        row["record_id"], row["created_at_utc"], row.get("reviewer"),
        row["source_filename"], row["source_sha256"], row["source_size_bytes"],
        row["ruleset_version"], row["fed_ruleset_version"], row["app_version"],
        row["parsing_method"], row["max_pages_scanned"], int(row["ocr_used"]),
        int(row["flagged"]), int(row["review_needed"]), row.get("reasons"),
        row.get("expiration_date"), row.get("effective_expiration_date"), row.get("test_date"),
        row.get("earliest_date_found"),
        int(row.get("expired_before_cutoff", False)),
        int(row.get("expired_as_of_scan", False)),
        int(row.get("has_early_date", False)),
        int(row["hemp_flag"]), row.get("hemp_severity"), row.get("hemp_reasons"),
        row.get("hemp_delta9_pct"), row.get("hemp_thca_pct"), row.get("hemp_total_thc_pct"),
        row.get("potency_json"), row.get("evidence_json"), int(row.get("percent_map_count", 0))
    ))
    conn.commit()


def db_insert_event(record_id: str, event_type: str, payload: dict):
    conn = get_db_conn()
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


# ============================
# OCR + image preprocessing
# ============================
def _preprocess_for_ocr(img: Image.Image, mode: str = "thresh") -> Image.Image:
    """
    mode:
      - "gray": light cleanup
      - "thresh": binarize for most COAs
      - "invthresh": inverted binarize (rescues faint / inverted scans)
    """
    g = img.convert("L")
    g = ImageOps.autocontrast(g)
    g = g.filter(ImageFilter.UnsharpMask(radius=2, percent=160, threshold=3))

    if mode == "thresh":
        g = g.point(lambda x: 255 if x > 185 else 0)
    elif mode == "invthresh":
        g = g.point(lambda x: 0 if x > 185 else 255)
    return g


def render_pdf_pages_with_pdfium(pdf_bytes: bytes, page_indices_0: List[int], scale: float) -> List[Tuple[int, Image.Image]]:
    out: List[Tuple[int, Image.Image]] = []
    pdf = pdfium.PdfDocument(pdf_bytes)
    n = len(pdf)
    for i0 in page_indices_0:
        if 0 <= i0 < n:
            page = pdf[i0]
            out.append((i0, page.render(scale=scale).to_pil()))
    return out


def ocr_text_images(images: List[Tuple[int, Image.Image]], psm: int) -> str:
    config = f"--oem 1 --psm {psm} -c preserve_interword_spaces=1"
    chunks = []
    for _, img in images:
        chunks.append(pytesseract.image_to_string(_preprocess_for_ocr(img, "thresh"), config=config))
    return "\n\n".join(chunks).strip()


def quick_table_crop(img: Image.Image) -> Optional[Tuple[int, int, int, int]]:
    """
    Fast table-region crop based on detecting header tokens like:
      Compound/Cannabinoid/Terpene/LOD/LOQ/Percent/%
    Returns (l, t, r, b) in original image coordinates.
    """
    W, H = img.size
    smallW = max(1, int(W * 0.5))
    smallH = max(1, int(H * 0.5))
    small = img.resize((smallW, smallH))
    sx = W / float(smallW)
    sy = H / float(smallH)

    d = pytesseract.image_to_data(
        _preprocess_for_ocr(small, "gray"),
        output_type=Output.DICT,
        config="--oem 1 --psm 11 -c preserve_interword_spaces=1",
    )

    hits_y: List[int] = []
    for i, txt in enumerate(d.get("text", [])):
        t = (txt or "").strip().lower()
        if not t:
            continue
        if re.search(r"\b(compound|cannabinoid|cannabinoids|terpene|terpenes|lod|loq|percent|%)\b", t, re.I):
            hits_y.append(int(d["top"][i]))

    if not hits_y:
        return None

    top = int(min(hits_y) * sy)

    t0 = max(0, top - 250)
    b0 = min(H, t0 + int(H * 0.70))
    return (0, t0, W, b0)


def ocr_data_images_mode(images: List[Tuple[int, Image.Image]], psm: int, mode: str) -> List[Dict[str, Any]]:
    config = f"--oem 1 --psm {psm} -c preserve_interword_spaces=1"
    out: List[Dict[str, Any]] = []
    for page0, img in images:
        crop = quick_table_crop(img)
        img2 = img.crop(crop) if crop else img
        d = pytesseract.image_to_data(_preprocess_for_ocr(img2, mode), output_type=Output.DICT, config=config)
        d["__page0__"] = page0
        d["__crop__"] = crop
        d["__mode__"] = mode
        d["__psm__"] = psm
        out.append(d)
    return out


# ============================
# PDF text extraction + relevant pages
# ============================
KEYWORDS = [
    "percent", "%", "cannabinoid", "concentration", "potency", "delta", "thc", "thca",
    "analysis completed", "date of analysis", "test date", "results",
]


def extract_text_pdfplumber_pages(pdf_bytes: bytes, max_pages: int) -> List[str]:
    pages: List[str] = []
    with pdfplumber.open(io.BytesIO(pdf_bytes)) as pdf:
        for p in pdf.pages[:max_pages]:
            pages.append((p.extract_text() or "").strip())
    return pages


def choose_relevant_pages_from_text(page_texts: List[str], max_pick: int) -> List[int]:
    scored: List[Tuple[int, int]] = []
    for idx, txt in enumerate(page_texts):
        t = _norm(txt)
        score = 0
        for kw in KEYWORDS:
            if kw in t:
                score += 3
        score += min(10, len(txt) // 800)
        scored.append((score, idx))
    scored.sort(reverse=True)
    picks = [idx for score, idx in scored if score > 0][:max_pick]
    if not picks:
        picks = list(range(min(max_pick, len(page_texts))))
    return sorted(set(picks))


def extract_text_hybrid(
    pdf_bytes: bytes,
    page_indices_0: List[int],
    min_text_len: int,
    ocr_scale: float,
) -> Tuple[str, str, bool]:
    page_texts: List[str] = []
    with pdfplumber.open(io.BytesIO(pdf_bytes)) as pdf:
        n_pages = len(pdf.pages)
        for i0 in page_indices_0:
            if 0 <= i0 < n_pages:
                page_texts.append(pdf.pages[i0].extract_text() or "")
    text = "\n\n".join(page_texts).strip()
    if len(text) >= min_text_len:
        return text, "pdf_text", False

    images = render_pdf_pages_with_pdfium(pdf_bytes, page_indices_0, scale=ocr_scale)
    o1 = ocr_text_images(images, psm=6)
    o2 = ocr_text_images(images, psm=11)
    return (text + "\n\n" + o1 + "\n\n" + o2).strip(), "hybrid_text+ocr", True


# ============================
# Dates (Analysis Completed primary)
# ============================
MONTH_NAME_RE = r"(?:jan(?:uary)?|feb(?:ruary)?|mar(?:ch)?|apr(?:il)?|may|jun(?:e)?|jul(?:y)?|aug(?:ust)?|sep(?:t(?:ember)?)?|oct(?:ober)?|nov(?:ember)?|dec(?:ember)?)"
DATE_TOKEN_NUMERIC = r"(?<![A-Za-z0-9-])(\d{1,2}[/-]\d{1,2}[/-]\d{2,4}|\d{4}-\d{2}-\d{2})(?![A-Za-z0-9-])"
DATE_TOKEN_TEXTUAL = rf"(?<![A-Za-z0-9-])({MONTH_NAME_RE}\s+\d{{1,2}}(?:,)?\s+\d{{4}}|\d{{1,2}}\s+{MONTH_NAME_RE}(?:,)?\s+\d{{4}})(?![A-Za-z0-9-])"

DATE_LABELS: List[Tuple[str, int, str]] = [
    ("analysis_completed", 1, r"\banalysis\s*completed\b|\banalysis\s*complete\b"),
    ("date_of_analysis", 1, r"\bdate\s*of\s*analysis\b|\banalysis\s*date\b|\bdate\s*analy(?:s|z)ed\b"),
    ("date_tested", 1, r"\bdate\s*tested\b|\btest\s*date\b"),
    ("report_date", 2, r"\breport\s*date\b|\bdate\s*of\s*report\b|\bcoa\s*date\b|\bissued\s*date\b|\bdate\s*issued\b|\bdate\s*reported\b|\breported\s*on\b"),
    ("date_received", 3, r"\bdate\s*received\b|\breceived\s*date\b"),
    ("collection_date", 3, r"\bcollection\s*date\b|\bsample\s*date\b"),
]


def extract_expiration_date(text: str) -> Tuple[Optional[date], Optional[DateEvidence]]:
    if not text:
        return None, None
    exp_label = r"(?:expiration\s*date|exp\s*date|expires?|expir\w*)"
    for tok_re in (DATE_TOKEN_NUMERIC, DATE_TOKEN_TEXTUAL):
        m = re.search(rf"{exp_label}\s*[:\-]?\s*(?:\n|\s){{0,60}}{tok_re}", text, flags=re.IGNORECASE)
        if m:
            d = safe_parse_date(m.group(1))
            if d:
                return d, DateEvidence(kind="expiration", value=d.isoformat(), source="regex", snippet=(m.group(0) or "")[:260])
    return None, None


def extract_labeled_dates_global(text: str) -> List[Tuple[date, DateEvidence, int]]:
    if not text:
        return []
    out: List[Tuple[date, DateEvidence, int]] = []
    window = 140

    for kind, rank, label_pat in DATE_LABELS:
        label_re = re.compile(label_pat, re.IGNORECASE)
        for lm in label_re.finditer(text):
            seg = text[lm.end(): lm.end() + window]
            for tok_re in (DATE_TOKEN_NUMERIC, DATE_TOKEN_TEXTUAL):
                dm = re.search(tok_re, seg, flags=re.IGNORECASE)
                if not dm:
                    continue
                d = safe_parse_date(dm.group(1))
                if not d:
                    continue
                snippet = (text[lm.start(): min(len(text), lm.end() + dm.end() + 30)]).replace("\n", " ")
                out.append((d, DateEvidence(kind=kind, value=d.isoformat(), source="regex", snippet=snippet[:260]), rank))
                break

    seen = set()
    uniq: List[Tuple[date, DateEvidence, int]] = []
    for d, ev, rank in out:
        k = (ev.kind, d.isoformat())
        if k in seen:
            continue
        seen.add(k)
        uniq.append((d, ev, rank))
    uniq.sort(key=lambda x: (x[2], x[0]))
    return uniq


def choose_best_analysis_completed_or_test_date(labeled: List[Tuple[date, DateEvidence, int]]) -> Optional[Tuple[date, DateEvidence]]:
    if not labeled:
        return None
    best_rank = min(r for _, _, r in labeled)
    candidates = [(d, ev) for d, ev, r in labeled if r == best_rank]
    if not candidates:
        return None
    return max(candidates, key=lambda x: x[0])


def compute_effective_expiration(exp_date: Optional[date], analysis_completed_date: Optional[date]) -> Tuple[Optional[date], Optional[DateEvidence]]:
    if exp_date:
        return exp_date, None
    if analysis_completed_date:
        eff = analysis_completed_date + timedelta(days=COA_VALIDITY_DAYS)
        return eff, DateEvidence(
            kind="derived_expiration_365",
            value=eff.isoformat(),
            source="derived",
            snippet=f"Derived: {analysis_completed_date.isoformat()} + {COA_VALIDITY_DAYS} days (Analysis Completed)",
        )
    return None, None


# ============================
# Potency extraction (tables + OCR layout + inline)
# ============================
ANALYTE_KEYS: Dict[str, List[str]] = {
    "delta8_pct": [
        r"\bdelta\s*[-]?\s*8\b", r"\bdelta8\b", r"delta\s*[-]?\s*8\s*thc\b",
        r"\bΔ\s*[-]?\s*8\b", r"\bΔ8\b", r"\bΔ\s*[-]?\s*8\s*thc\b", r"\bd8[-\s]*thc\b",
    ],
    "delta9_pct": [
        r"\bdelta\s*[-]?\s*9\b", r"\bdelta9\b", r"delta\s*[-]?\s*9\s*thc\b",
        r"\bΔ\s*[-]?\s*9\b", r"\bΔ9\b", r"\bΔ\s*[-]?\s*9\s*thc\b", r"\bd9[-\s]*thc\b",
    ],
    "thca_pct": [r"\bthca\b", r"thc[-\s]*a\b", r"tetrahydrocannabinolic"],
    "total_thc_pct": [r"\btotal\s*thc\b", r"\bthc\s*total\b", r"\bmax\s*active\s*thc\b", r"\btotal\s*active\s*thc\b"],
    "total_potential_thc_pct": [r"\btotal\s*potential\s*thc\b", r"\bpotential\s*thc\b"],
}

_ND_RE = re.compile(r"\bnd\b|n\.d\.|n/d|not\s+detected", re.IGNORECASE)
_NUM_RE = re.compile(r"(?<!\w)(\d+(?:\.\d+)?)(?!\w)")
_HAS_PERCENT = re.compile(r"%")
_HAS_MG_G = re.compile(r"\bmg\s*/?\s*g\b|\bmg\s+g\b", re.IGNORECASE)
_HAS_MG_KG = re.compile(r"\bmg\s*/?\s*kg\b", re.IGNORECASE)
_HAS_PPM = re.compile(r"\bppm\b", re.IGNORECASE)

DECARB_FORMULA_RE = re.compile(
    r"0\.877\s*(?:x|\*)\s*thc\s*[-\s]*a|0\.877\s*(?:x|\*)\s*thca|max\s*thc|decarb|decarbox|calculation|formula|factor",
    re.IGNORECASE,
)

INLINE_POTENCY_PATTERNS = {
    "delta8_pct": [r"(?:delta\s*[-]?\s*8|Δ\s*[-]?\s*8|Δ8|d8)\s*(?:thc)?\s*[:\-]?\s*(nd|n\.d\.|n/d|not detected|\d+(?:\.\d+)?)\s*%"],
    "delta9_pct": [r"(?:delta\s*[-]?\s*9|Δ\s*[-]?\s*9|Δ9|d9)\s*(?:thc)?\s*[:\-]?\s*(nd|n\.d\.|n/d|not detected|\d+(?:\.\d+)?)\s*%"],
    "thca_pct": [r"\bthc[\s\-]*a\b\s*[:\-]?\s*(nd|n\.d\.|n/d|not detected|\d+(?:\.\d+)?)\s*%"],
    "total_thc_pct": [r"\btotal\s*thc\b\s*[:\-]?\s*(nd|n\.d\.|n/d|not detected|\d+(?:\.\d+)?)\s*%"],
    "total_potential_thc_pct": [r"\btotal\s*potential\s*thc\b\s*[:\-]?\s*(nd|n\.d\.|n/d|not detected|\d+(?:\.\d+)?)\s*%"],
}


def _match_analyte_key(s: str) -> Optional[str]:
    s2 = _norm_analyte(s)
    for k, pats in ANALYTE_KEYS.items():
        for p in pats:
            if re.search(p, s2, flags=re.IGNORECASE):
                return k
    return None


def _normalize_to_percent_raw_from_header(raw: float) -> Tuple[Optional[float], str, str]:
    if raw < 0:
        return None, "low", "negative_value"
    if raw <= 100.0:
        return raw, "high", "header_anchored_percent_col"
    return None, "low", "header_anchored_out_of_range"


def _normalize_to_percent(raw: float, line: str) -> Tuple[Optional[float], str, str]:
    if raw < 0:
        return None, "low", "negative_value"

    if _HAS_PERCENT.search(line):
        return (raw, "high", "explicit_percent") if raw <= 100.0 else (None, "low", "explicit_percent_out_of_range")

    if _HAS_MG_G.search(line):
        pct = raw / 10.0
        return (pct, "high", "unit_mg_per_g_div10") if pct <= 100.0 else (None, "low", "mg_g_out_of_range")

    if _HAS_MG_KG.search(line) or _HAS_PPM.search(line):
        pct = raw / 10000.0
        return (pct, "high", "unit_ppm_or_mgkg_div10000") if pct <= 100.0 else (None, "low", "mgkg_out_of_range")

    if raw > 100.0:
        return None, "low", "no_unit_gt_100_rejected"

    if 20.0 < raw <= 100.0:
        return raw / 10.0, "medium", "no_unit_assumed_mg_g_div10"

    return None, "low", "no_unit_ambiguous_le_20_rejected"


def _extract_row_value(line: str) -> Tuple[Optional[float], str, str, str]:
    nums = [float(x) for x in _NUM_RE.findall(line)]
    if not nums:
        if _ND_RE.search(line):
            return 0.0, ("high" if _HAS_PERCENT.search(line) else "medium"), "nd_no_numbers", "ND"
        return None, "none", "no_numbers", ""
    raw = nums[1] if len(nums) >= 2 else nums[0]
    pct, conf, notes = _normalize_to_percent(raw, line)
    return pct, conf, notes, str(raw)


def extract_percent_map_from_tables(pdf_bytes: bytes, page_indices_0: List[int]) -> Tuple[Dict[str, Dict[str, Any]], List[PotencyEvidence]]:
    out: Dict[str, Dict[str, Any]] = {}
    evs: List[PotencyEvidence] = []
    with pdfplumber.open(io.BytesIO(pdf_bytes)) as pdf:
        n_pages = len(pdf.pages)
        for i0 in page_indices_0:
            if not (0 <= i0 < n_pages):
                continue
            page = pdf.pages[i0]
            page_idx = i0 + 1
            try:
                tables = page.extract_tables() or []
            except Exception:
                tables = []

            for table in tables:
                if not table or len(table) < 2:
                    continue
                header = table[0]
                header_norm = [_norm(h) for h in header]

                pct_idx = None
                loq_idx = None
                for i, h in enumerate(header_norm):
                    if h in ["%", "percent", "% w/w", "%ww", "percent w/w", "percent (w/w)"] or ("percent" in h) or ("%" in h and "loq" not in h):
                        pct_idx = i
                    if "loq" in h:
                        loq_idx = i

                if pct_idx is None:
                    continue

                name_idx = 0
                for i, h in enumerate(header_norm):
                    if any(k in h for k in ["analyte", "compound", "cannabinoid", "name", "concentration"]):
                        name_idx = i
                        break

                for row in table[1:]:
                    if not row or len(row) <= max(name_idx, pct_idx):
                        continue
                    raw_name = (row[name_idx] or "").strip()
                    if not raw_name:
                        continue
                    key = _match_analyte_key(raw_name)
                    if not key:
                        continue

                    row_join = " ".join([str(x) for x in row if x is not None])
                    if DECARB_FORMULA_RE.search(row_join):
                        continue

                    raw_val_cell = row[pct_idx]
                    raw_val = _parse_float_or_nd(raw_val_cell)
                    if raw_val is None:
                        continue

                    loq_val = None
                    if loq_idx is not None and loq_idx < len(row):
                        loq_val = _parse_float_or_nd(row[loq_idx])

                    pct, conf, notes = _normalize_to_percent(float(raw_val), row_join)
                    evs.append(PotencyEvidence(
                        key=key, value_pct=pct, source="table", confidence=conf, page=page_idx,
                        raw_name=raw_name[:120], raw_value=str(raw_val_cell)[:80],
                        snippet=row_join[:240], notes=(notes + (f"; loq={loq_val}" if loq_val is not None else ""))
                    ))

                    if pct is None:
                        continue
                    prev = out.get(key, {}).get("pct")
                    if prev is None or pct > float(prev):
                        out[key] = {
                            "pct": pct,
                            "loq": float(loq_val) if loq_val is not None else None,
                            "source": "table",
                            "page": page_idx,
                            "confidence": conf,
                            "raw_name": raw_name,
                            "raw_value": str(raw_val_cell),
                            "snippet": row_join[:240],
                            "notes": notes,
                        }
    return out, evs


def extract_percent_map_from_text_rows(text: str) -> Tuple[Dict[str, Dict[str, Any]], List[PotencyEvidence]]:
    out: Dict[str, Dict[str, Any]] = {}
    evs: List[PotencyEvidence] = []
    if not text:
        return out, evs

    for ln in (ln.strip() for ln in text.splitlines() if ln.strip()):
        if len(ln) < 6:
            continue
        if re.search(r"prepared\s+for|final\s+authorization|remarks|page\s+\d+\s+of|\bcoa\b", ln, re.I):
            continue
        if DECARB_FORMULA_RE.search(ln):
            continue

        key = _match_analyte_key(ln)
        if not key:
            continue

        pct, conf, notes, raw_value = _extract_row_value(ln)
        evs.append(PotencyEvidence(
            key=key, value_pct=pct, source="ocr_row", confidence=conf,
            raw_name=key, raw_value=raw_value[:80], snippet=ln[:240], notes=notes
        ))

        if pct is None:
            continue
        prev = out.get(key, {}).get("pct")
        if prev is None or pct > float(prev):
            out[key] = {"pct": pct, "loq": None, "source": "ocr_row", "page": None, "confidence": conf,
                        "raw_name": key, "raw_value": raw_value, "snippet": ln[:240], "notes": notes}
    return out, evs


def _parse_percent_token(tok: str) -> Tuple[Optional[float], str]:
    t = (tok or "").strip()
    if not t:
        return None, "empty"

    t = t.replace(",", "").strip()

    if t.endswith("%"):
        t = t[:-1].strip()

    t = re.sub(r"[^\d\.<]+$", "", t).strip()

    if _ND_RE.fullmatch(t) or _ND_RE.search(t):
        return 0.0, "nd"

    m = re.fullmatch(r"(<)?\s*(\d+(?:\.\d+)?)", t)
    if not m:
        return None, "not_numeric"

    val = float(m.group(2))
    return (val, "less_than") if m.group(1) else (val, "numeric")


def extract_percent_map_from_ocr_layout(
    ocr_pages_data: List[Dict[str, Any]]
) -> Tuple[Dict[str, Dict[str, Any]], List[PotencyEvidence]]:
    """
    Improved:
    - Anchors LOQ + Percent columns (handles 'Percent' and '%')
    - Extracts percent ONLY within a percent-column window (prevents LOQ bleed)
    - Captures LOQ per-row when possible; stores it into map for later gating
    - Accepts split headers (LOQ and Percent on adjacent lines)
    """
    out: Dict[str, Dict[str, Any]] = {}
    evs: List[PotencyEvidence] = []

    def build_words(d: Dict[str, Any]) -> List[dict]:
        n = len(d.get("text", []))
        words: List[dict] = []
        for i in range(n):
            txt = (d["text"][i] or "").strip()
            if not txt:
                continue
            conf = float(d["conf"][i]) if str(d["conf"][i]).replace(".", "", 1).isdigit() else -1.0
            if 0 <= conf < 35:
                continue
            x, y, w, h = int(d["left"][i]), int(d["top"][i]), int(d["width"][i]), int(d["height"][i])
            words.append({"t": txt, "x": x, "y": y, "w": w, "h": h, "xc": x + w / 2.0})
        return words

    def cluster_lines(words: List[dict], y_tol: int = 14) -> List[List[dict]]:
        words.sort(key=lambda z: (z["y"], z["x"]))
        lines: List[List[dict]] = []
        for w in words:
            if not lines:
                lines.append([w])
                continue
            if abs(w["y"] - lines[-1][0]["y"]) <= y_tol:
                lines[-1].append(w)
            else:
                lines.append([w])
        return lines

    def line_text(ws: List[dict]) -> str:
        ws2 = sorted(ws, key=lambda z: z["x"])
        return " ".join(z["t"] for z in ws2)

    def _xs_for(ws: List[dict], pat: str) -> List[float]:
        xs: List[float] = []
        for z in ws:
            if re.search(pat, z["t"], flags=re.I):
                xs.append(float(z["xc"]))
        return xs

    def find_header_anchors(lines: List[List[dict]]) -> Optional[Dict[str, float]]:
        for i, ws in enumerate(lines[:70]):
            s = _norm(line_text(ws))
            if not (("loq" in s) and (("percent" in s) or ("%" in s))):
                continue
            loq_xs = _xs_for(ws, r"^loq$")
            pct_xs = _xs_for(ws, r"%|percent")
            if not loq_xs or not pct_xs:
                continue
            x_loq = float(sorted(loq_xs)[len(loq_xs) // 2])
            pct_right = [x for x in pct_xs if x > x_loq + 10]
            x_pct = float(sorted(pct_right)[len(pct_right) // 2]) if pct_right else float(sorted(pct_xs)[len(pct_xs) // 2])
            return {"header_idx": float(i), "x_loq": x_loq, "x_pct": x_pct}

        loq_candidates: List[Tuple[int, float]] = []
        pct_candidates: List[Tuple[int, float]] = []
        for i, ws in enumerate(lines[:80]):
            s = _norm(line_text(ws))
            if "loq" in s:
                xs = _xs_for(ws, r"^loq$")
                if xs:
                    loq_candidates.append((i, float(sorted(xs)[len(xs) // 2])))
            if ("percent" in s) or ("%" in s):
                xs = _xs_for(ws, r"%|percent")
                if xs:
                    pct_candidates.append((i, float(sorted(xs)[len(xs) // 2])))

        best: Optional[Dict[str, float]] = None
        for i_loq, x_loq in loq_candidates:
            for i_pct, x_pct0 in pct_candidates:
                if abs(i_loq - i_pct) <= 2:
                    header_idx = float(min(i_loq, i_pct))
                    x_pct = x_pct0
                    if x_pct <= x_loq + 10:
                        ws = lines[i_pct]
                        xs = _xs_for(ws, r"%|percent")
                        if xs:
                            x_pct = float(max(xs))
                    cand = {"header_idx": header_idx, "x_loq": float(x_loq), "x_pct": float(x_pct)}
                    if best is None or cand["header_idx"] < best["header_idx"]:
                        best = cand
        return best

    def parse_row(ws: List[dict], anchors: Dict[str, float]) -> Optional[Tuple[str, float, Optional[float], str, str]]:
        x_loq = anchors["x_loq"]
        x_pct = anchors["x_pct"]

        loq_window = 110
        pct_left = (x_loq + x_pct) / 2.0
        pct_right = x_pct + 160

        left_tokens = [z for z in ws if z["xc"] < pct_left - 8]
        if not left_tokens:
            return None

        raw_name = " ".join(z["t"] for z in sorted(left_tokens, key=lambda z: z["x"])).strip()
        key = _match_analyte_key(raw_name)
        if not key:
            return None

        loq_val = None
        loq_candidates = [z for z in ws if abs(z["xc"] - x_loq) <= loq_window]
        if loq_candidates:
            loq_candidates.sort(key=lambda z: abs(z["xc"] - x_loq))
            v, _note = _parse_percent_token(loq_candidates[0]["t"])
            if v is not None:
                loq_val = float(v)

        pct_candidates = [z for z in ws if (z["xc"] >= pct_left) and (z["xc"] <= pct_right)]
        scored: List[Tuple[float, float, str, str]] = []
        for z in pct_candidates:
            v, note = _parse_percent_token(z["t"])
            if v is None:
                continue
            scored.append((abs(z["xc"] - x_pct), float(v), z["t"], note))

        if not scored:
            pct_candidates2 = [z for z in ws if (z["xc"] >= pct_left)]
            for z in pct_candidates2:
                v, note = _parse_percent_token(z["t"])
                if v is None:
                    continue
                scored.append((abs(z["xc"] - x_pct), float(v), z["t"], note))

        if not scored:
            return None

        scored.sort(key=lambda x: x[0])
        _, raw_num, raw_tok, note = scored[0]

        pct, _conf, notes = _normalize_to_percent_raw_from_header(raw_num)
        if pct is None:
            return None

        return (key, float(pct), loq_val, raw_tok, raw_name)

    for d in ocr_pages_data:
        page0 = int(d.get("__page0__", -1))
        page_idx = page0 + 1 if page0 >= 0 else None

        words = build_words(d)
        if not words:
            continue

        lines = cluster_lines(words)
        anchors = find_header_anchors(lines)
        if not anchors:
            continue

        header_idx = int(anchors["header_idx"])

        for ws in lines[header_idx + 1:]:
            s = line_text(ws)
            if len(s) < 4:
                continue
            if DECARB_FORMULA_RE.search(s):
                continue

            parsed = parse_row(ws, anchors)
            if not parsed:
                continue

            key, pct_val, loq_val, raw_tok, raw_name = parsed

            evs.append(PotencyEvidence(
                key=key,
                value_pct=pct_val,
                source="ocr_layout",
                confidence="high",
                page=page_idx,
                raw_name=raw_name[:120],
                raw_value=str(raw_tok)[:40],
                snippet=s[:240],
                notes=("header_anchored_percent_col" + (f"; loq={loq_val}" if loq_val is not None else "")),
            ))

            prev = out.get(key, {}).get("pct")
            if prev is None or pct_val > float(prev):
                out[key] = {
                    "pct": pct_val,
                    "loq": float(loq_val) if loq_val is not None else None,
                    "source": "ocr_layout",
                    "page": page_idx,
                    "confidence": "high",
                    "raw_name": raw_name,
                    "raw_value": str(raw_tok),
                    "snippet": s[:240],
                    "notes": ("header_anchored_percent_col" + (f"; loq={loq_val}" if loq_val is not None else "")),
                }

    return out, evs


def extract_inline_potency(text: str) -> List[PotencyEvidence]:
    if not text or "%" not in text:
        return []
    out: List[PotencyEvidence] = []
    for key, pats in INLINE_POTENCY_PATTERNS.items():
        best: Optional[Tuple[float, str]] = None
        for pat in pats:
            for m in re.finditer(pat, text, flags=re.IGNORECASE | re.DOTALL):
                raw = (m.group(1) or "").strip()
                val = _parse_float_or_nd(raw)
                if val is None:
                    continue
                snippet = (m.group(0) or "")[:240]
                if best is None or float(val) > best[0]:
                    best = (float(val), snippet)
        if best is not None:
            out.append(PotencyEvidence(
                key=key, value_pct=best[0], source="inline_text", confidence="high",
                raw_name=key, raw_value=str(best[0]), snippet=best[1], notes="explicit_percent_inline",
            ))
    return out


def combine_percent_maps(*maps: Dict[str, Dict[str, Any]]) -> Dict[str, Dict[str, Any]]:
    out: Dict[str, Dict[str, Any]] = {}
    for m in maps:
        for k, v in (m or {}).items():
            if k not in out:
                out[k] = v
            else:
                try:
                    if float(v.get("pct")) > float(out[k].get("pct")):
                        out[k] = v
                except Exception:
                    pass
    return out


def extract_potency_from_map(percent_map: Dict[str, Dict[str, Any]]) -> Tuple[Dict[str, Optional[float]], Dict[str, str]]:
    potency: Dict[str, Optional[float]] = {}
    conf: Dict[str, str] = {}

    keys = ["delta8_pct", "delta9_pct", "thca_pct", "total_thc_pct", "total_potential_thc_pct"]
    for k in keys:
        if k in percent_map:
            pct = float(percent_map[k]["pct"])
            loq = percent_map[k].get("loq")

            try:
                if loq is not None and pct < float(loq):
                    pct = 0.0
                    conf[k] = "high"
                else:
                    conf[k] = str(percent_map[k].get("confidence") or "unknown")
            except Exception:
                conf[k] = str(percent_map[k].get("confidence") or "unknown")

            potency[k] = pct
        else:
            potency[k] = None
            conf[k] = "none"

    if potency.get("total_thc_pct") is None:
        d9 = float(potency.get("delta9_pct") or 0.0)
        a = float(potency.get("thca_pct") or 0.0)
        if d9 or a:
            potency["total_thc_pct"] = d9 + (a * THCA_DECARB_FACTOR)
            conf["total_thc_pct"] = "computed"

    if potency.get("total_thc_pct") is None and potency.get("total_potential_thc_pct") is not None:
        potency["total_thc_pct"] = float(potency["total_potential_thc_pct"])
        conf["total_thc_pct"] = "high"

    return potency, conf


def thc_over_threshold_litigation(
    potency: Dict[str, Optional[float]],
    conf: Dict[str, str],
    threshold: float
) -> Tuple[bool, List[str], bool]:
    evidence: List[str] = []
    review_needed = False

    for k in ["total_thc_pct", "delta9_pct", "thca_pct", "delta8_pct", "total_potential_thc_pct"]:
        v = potency.get(k)
        if v is None:
            continue
        c = conf.get(k, "none")
        evidence.append(f"{k}={float(v):.3f}% (conf={c})")
        if c in ("high", "computed"):
            if float(v) > threshold:
                return True, evidence, review_needed
        else:
            review_needed = True

    if not evidence:
        evidence.append("No potency extracted")
        review_needed = True

    return False, evidence, review_needed


# ============================
# Federal hemp
# ============================
def evaluate_federal_hemp_from_potency(
    potency: Dict[str, Optional[float]],
    delta9_limit: float,
    total_limit: float,
    negligent_cutoff: float,
) -> Tuple[bool, Dict[str, Any]]:
    d9 = potency.get("delta9_pct")
    thca = potency.get("thca_pct")
    total = potency.get("total_thc_pct")

    reasons: List[str] = []
    severity = "none"

    if d9 is not None and float(d9) > delta9_limit:
        reasons.append(f"Delta-9 THC exceeds {delta9_limit}% (delta-9 = {float(d9):.3f}%)")
        severity = "breach"

    if total is not None and float(total) > total_limit:
        reasons.append(f"Total THC exceeds {total_limit}% (total = {float(total):.3f}%)")
        severity = "breach"

    if total is not None and float(total) > negligent_cutoff:
        reasons.append(f"Total THC exceeds {negligent_cutoff}% (total = {float(total):.3f}%)")
        severity = "elevated"

    if d9 is None and total is None:
        reasons.append("No reliable Delta-9/Total THC % found")
        severity = "unknown"

    return severity in ("breach", "elevated"), {
        "reasons": reasons,
        "severity": severity,
        "delta9_pct": d9,
        "thca_pct": thca,
        "total_thc_pct": total,
    }


# ============================
# Client flag (strict + conservative)
# ============================
def evaluate_client_flag_litigation(
    text: str,
    potency: Dict[str, Optional[float]],
    conf: Dict[str, str],
    strict_dates_only: bool,
    scan_date: date,
) -> Tuple[bool, bool, Dict[str, Any]]:
    reasons: List[str] = []
    evidence: Dict[str, Any] = {}

    has_delta8 = any_term(text, DELTA8_TERMS) or (potency.get("delta8_pct") is not None)
    has_delta9 = any_term(text, DELTA9_TERMS) or (potency.get("delta9_pct") is not None)
    has_delta = bool(has_delta8 or has_delta9)
    has_thc_context = any_term(text, THC_CONTEXT_TERMS) or any(v is not None for v in potency.values())

    thc_over, thc_ev, potency_review = thc_over_threshold_litigation(potency, conf, CLIENT_THC_THRESHOLD)

    exp_date, exp_ev = extract_expiration_date(text)
    labeled = extract_labeled_dates_global(text)
    best = choose_best_analysis_completed_or_test_date(labeled)
    analysis_completed_date = best[0] if best else None
    analysis_ev = best[1] if best else None

    eff_exp_date, derived_ev = compute_effective_expiration(exp_date, analysis_completed_date)

    expired_before_cutoff = bool(eff_exp_date and eff_exp_date < EXPIRY_CUTOFF)
    expired_as_of_scan = bool(eff_exp_date and eff_exp_date < scan_date)

    early_labeled = [d for (d, _, _) in labeled if d.year <= EARLY_YEAR_CUTOFF]
    has_early_date = bool(early_labeled)

    if strict_dates_only and (not exp_date) and (not labeled):
        reasons.append("STRICT DATE MODE: insufficient date evidence (no explicit expiration and no label-anchored date)")
        date_condition = False
        date_review = True
    else:
        date_condition = expired_before_cutoff or has_early_date
        date_review = False if (exp_date or labeled) else True

    reasons.append("Delta 8/9 detected" if has_delta else "No Delta 8/9 detected")
    reasons.append("THC context detected" if has_thc_context else "No THC context detected")
    reasons.append(f"THC above {CLIENT_THC_THRESHOLD}% detected" if thc_over else f"No THC above {CLIENT_THC_THRESHOLD}% detected")

    reasons.append(f"Explicit expiration date found: {exp_date.isoformat()}" if exp_date else "No explicit expiration date found")
    reasons.append(
        f"Analysis Completed / primary date found: {analysis_completed_date.isoformat()}"
        if analysis_completed_date else
        "No label-anchored Analysis Completed/Test/Analysis date found"
    )
    reasons.append(f"Effective expiration date: {eff_exp_date.isoformat()}" if eff_exp_date else "No effective expiration date available")

    if expired_before_cutoff:
        reasons.append(f"Expired before cutoff {EXPIRY_CUTOFF.isoformat()} (effective expiration)")
    if expired_as_of_scan:
        reasons.append(f"Expired as of scan date {scan_date.isoformat()} (effective expiration)")

    if has_early_date:
        reasons.append(f"Contains label-anchored date in {EARLY_YEAR_CUTOFF} or earlier (e.g., {min(early_labeled).isoformat()})")

    if not date_condition:
        reasons.append(
            f"Date condition not met (needs expired-before-cutoff using effective expiration OR label-anchored date in {EARLY_YEAR_CUTOFF} or earlier)"
        )

    flagged = bool(has_delta and has_thc_context and thc_over and date_condition)
    review_needed = bool(potency_review or date_review)

    earliest_found = ""
    if early_labeled:
        earliest_found = min(early_labeled).isoformat()
    elif labeled:
        earliest_found = labeled[0][0].isoformat()

    evidence["thc_over_evidence"] = thc_ev
    evidence["expiration_evidence"] = asdict(exp_ev) if exp_ev else None
    evidence["derived_expiration_evidence"] = asdict(derived_ev) if derived_ev else None
    evidence["best_analysis_completed_evidence"] = asdict(analysis_ev) if analysis_ev else None
    evidence["labeled_date_evidence"] = [asdict(ev) for _, ev, _ in labeled[:12]]
    evidence["potency_confidence"] = conf

    details = {
        "has_delta8": has_delta8,
        "has_delta9": has_delta9,
        "scan_date": scan_date.isoformat(),
        "test_date": analysis_completed_date.isoformat() if analysis_completed_date else "",
        "expiration_date": exp_date.isoformat() if exp_date else "",
        "effective_expiration_date": eff_exp_date.isoformat() if eff_exp_date else "",
        "earliest_date_found": earliest_found,
        "expired_before_cutoff": expired_before_cutoff,
        "expired_as_of_scan": expired_as_of_scan,
        "has_early_date": has_early_date,
        "strict_dates_only": strict_dates_only,
        "used_labeled_dates": bool(labeled),
        "potency": potency,
        "evidence": evidence,
    }
    return flagged, review_needed, {"reasons": reasons, "details": details}


# ============================
# PDF report generator + Executive Summary
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


def _count_true(rows: Iterable[dict], key: str) -> int:
    return sum(1 for r in rows if bool(r.get(key)) is True)


def _nonempty(rows: Iterable[dict], key: str) -> int:
    return sum(1 for r in rows if str(r.get(key) or "").strip() != "")


def _classify_review_reasons(reason_text: str) -> List[str]:
    t = (reason_text or "").lower()
    buckets: List[str] = []

    if "strict date mode" in t or "insufficient date evidence" in t:
        buckets.append("Insufficient date evidence (strict mode)")
    if "no potency extracted" in t:
        buckets.append("Potency evidence missing/low confidence")
    if "no explicit expiration date found" in t and "no label-anchored" in t:
        buckets.append("No expiration + no analysis/test date located")
    if "date condition not met" in t:
        buckets.append("Date condition not met")
    if "error:" in t:
        buckets.append("Processing error")

    return buckets or ["Other / mixed"]


def _build_executive_summary(rows: List[Dict[str, Any]]) -> Tuple[str, str, List[str]]:
    total = len(rows)
    client_flagged = _count_true(rows, "flagged")
    review_needed = _count_true(rows, "review_needed")
    hemp_flagged = _count_true(rows, "hemp_flag")

    hemp_sev = Counter((r.get("hemp_severity") or "none") for r in rows)
    breach = hemp_sev.get("breach", 0)
    elevated = hemp_sev.get("elevated", 0)
    unknown = hemp_sev.get("unknown", 0)

    pct_map_ok = sum(1 for r in rows if int(r.get("percent_map_count") or 0) > 0)
    test_date_ok = _nonempty(rows, "test_date")
    eff_exp_ok = _nonempty(rows, "effective_expiration_date")

    review_reason_counts = Counter()
    for r in rows:
        if not bool(r.get("review_needed")):
            continue
        for b in _classify_review_reasons(r.get("reasons") or ""):
            review_reason_counts[b] += 1

    top_review = review_reason_counts.most_common(3)
    top_review_txt = ", ".join(f"{k} ({v})" for k, v in top_review) if top_review else "n/a"

    p1 = (
        f"This batch scan evaluated {total} PDF COAs using an evidence-first extraction workflow designed for defensible review. "
        f"{client_flagged} COAs ({_pct(client_flagged, total)}) met the client flag criteria, "
        f"{hemp_flagged} COAs ({_pct(hemp_flagged, total)}) triggered federal hemp checks, and "
        f"{review_needed} COAs ({_pct(review_needed, total)}) were marked 'review needed' due to missing or low-confidence evidence."
    )

    p2 = (
        "Interpretation notes: 'Client flagged' indicates the COA met the rule logic "
        "(Delta-8/Delta-9 present, THC above threshold, and an applicable date condition). "
        "'Review needed' does not automatically mean non-compliance; it means the scanner could not obtain litigation-grade, "
        "high-confidence evidence for one or more key fields (typically the analysis/test date or percent-column potency) "
        "and therefore requires a human confirmation. "
        "When an explicit expiration date is not present, the report derives an effective expiration as "
        "'Analysis Completed' + 365 days (common cannabis practice)."
    )

    bullets = [
        f"Potency extraction coverage: {pct_map_ok}/{total} ({_pct(pct_map_ok, total)}) had at least one usable percent-column row parsed.",
        f"Date extraction coverage: {test_date_ok}/{total} ({_pct(test_date_ok, total)}) contained an 'Analysis Completed/Test/Analysis' date; "
        f"{eff_exp_ok}/{total} ({_pct(eff_exp_ok, total)}) produced an effective expiration date.",
        f"Federal hemp outcomes: breach={breach} ({_pct(breach, total)}), elevated={elevated} ({_pct(elevated, total)}), unknown={unknown} ({_pct(unknown, total)}).",
        f"Most common 'review needed' drivers: {top_review_txt}.",
    ]
    return p1, p2, bullets


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
    review_ct = sum(1 for r in rows if r.get("review_needed") is True)
    hemp_flagged = sum(1 for r in rows if r.get("hemp_flag") is True)

    created = utc_now_iso()

    c.setFont("Helvetica-Bold", 18)
    c.drawString(x, y, f"{APP_NAME} — Batch Report")
    y -= 22

    c.setFont("Helvetica", 10)
    c.drawString(x, y, f"Generated (UTC): {created}")
    y -= 12
    c.drawString(x, y, f"App: {APP_VERSION} | Rulesets: {RULESET_VERSION} / {FED_RULESET_VERSION}")
    y -= 12
    c.drawString(
        x, y,
        f"Scanned: {total} | Client-flagged: {client_flagged} ({_pct(client_flagged, total)}) | "
        f"Review-needed: {review_ct} ({_pct(review_ct, total)}) | "
        f"Hemp-flagged: {hemp_flagged} ({_pct(hemp_flagged, total)})"
    )
    y -= 16

    c.setFont("Helvetica-Bold", 12)
    c.drawString(x, y, "Executive Summary")
    y -= 14

    p1, p2, bullets = _build_executive_summary(rows)
    c.setFont("Helvetica", 10)
    y = wrap_text(c, p1, x, y, max_w, size=10, leading=13)
    y -= 4
    y = wrap_text(c, p2, x, y, max_w, size=10, leading=13)
    y -= 6

    c.setFont("Helvetica-Bold", 11)
    c.drawString(x, y, "Key findings")
    y -= 12
    c.setFont("Helvetica", 10)
    for b in bullets:
        y = wrap_text(c, f"• {b}", x, y, max_w, size=10, leading=13)
    y -= 10

    c.setFont("Helvetica-Bold", 12)
    c.drawString(x, y, "Flagged / Review-needed (details)")
    y -= 16

    focus_rows = [r for r in rows if (r.get("flagged") or r.get("review_needed") or r.get("hemp_flag"))]
    if not focus_rows:
        c.setFont("Helvetica", 11)
        c.drawString(x, y, "No PDFs matched the selected criteria.")
        c.save()
        return buf.getvalue()

    for r in focus_rows:
        if y < 1.2 * inch:
            c.showPage()
            y = height - margin

        c.setFont("Helvetica-Bold", 10)
        y = wrap_text(c, r["filename"], x, y, max_w, size=10, leading=12)

        c.setFont("Helvetica", 9)
        y = wrap_text(c, f"SHA-256: {r.get('sha256', '')}", x, y, max_w, size=9, leading=11)
        y = wrap_text(
            c,
            f"Extraction: {r.get('parsing_method', '')} (OCR: {bool(r.get('ocr_used'))}, pages: {r.get('max_pages_scanned')}, deep_used: {bool(r.get('deep_scan_used'))})",
            x, y, max_w, size=9, leading=11
        )

        if r.get("test_date"):
            y = wrap_text(c, f"Analysis Completed / primary date: {r['test_date']}", x, y, max_w, size=9, leading=11)
        if r.get("expiration_date"):
            y = wrap_text(c, f"Explicit expiration: {r['expiration_date']}", x, y, max_w, size=9, leading=11)
        if r.get("effective_expiration_date"):
            y = wrap_text(c, f"Effective expiration: {r['effective_expiration_date']}", x, y, max_w, size=9, leading=11)

        pot = r.get("potency") or {}
        y = wrap_text(
            c,
            "Potency: "
            f"total_thc={_fmt_pct(pot.get('total_thc_pct'))}  "
            f"delta9={_fmt_pct(pot.get('delta9_pct'))}  "
            f"thca={_fmt_pct(pot.get('thca_pct'))}  "
            f"delta8={_fmt_pct(pot.get('delta8_pct'))}  "
            f"total_potential_thc={_fmt_pct(pot.get('total_potential_thc_pct'))}",
            x, y, max_w, size=9, leading=11
        )

        if r.get("hemp_reasons"):
            y = wrap_text(c, f"Hemp notes: {r.get('hemp_reasons')}", x, y, max_w, size=9, leading=11)

        ev = r.get("evidence") or {}
        if ev.get("thc_over_evidence"):
            y = wrap_text(c, "THC evidence:", x, y, max_w, size=9, leading=11)
            for line in (ev["thc_over_evidence"] or [])[:6]:
                y = wrap_text(c, f"- {line}", x + 12, y, max_w - 12, size=9, leading=11)

        y = wrap_text(c, f"Reasons: {r.get('reasons', '')}", x, y, max_w, size=9, leading=11)
        y -= 8

    c.save()
    return buf.getvalue()


# ============================
# Scanning pipeline
# ============================
@dataclass(frozen=True)
class ScanSettings:
    primary_pages: int
    deep_pages: int
    max_pages_cap: int
    enable_deep_scan: bool
    enable_full_fallback: bool
    relevant_page_pick: int
    min_text_len: int
    ocr_scale: float
    strict_dates_only: bool
    enable_hemp: bool
    hemp_delta9_limit: float
    hemp_total_limit: float
    hemp_negligent_cutoff: float
    scan_date_iso: str


def _score_pass(passd: Dict[str, Any]) -> Tuple[int, int, int]:
    ev = passd.get("evidence") or {}
    has_date = int(bool(ev.get("expiration_evidence") or ev.get("best_analysis_completed_evidence") or ev.get("labeled_date_evidence")))
    conf = passd.get("confidence") or {}
    high_pot = sum(1 for c in conf.values() if c in ("high", "computed"))
    any_pot = sum(1 for v in (passd.get("potency") or {}).values() if v is not None)
    return has_date, high_pot, any_pot


def _run_pass(
    name: str,
    pdf_bytes: bytes,
    settings: ScanSettings,
    page_indices_0: List[int],
) -> Dict[str, Any]:
    try:
        text, method, ocr_used = extract_text_hybrid(
            pdf_bytes=pdf_bytes,
            page_indices_0=page_indices_0,
            min_text_len=settings.min_text_len,
            ocr_scale=settings.ocr_scale,
        )
    except Exception:
        images_txt = render_pdf_pages_with_pdfium(pdf_bytes, page_indices_0, scale=settings.ocr_scale)
        o1 = ocr_text_images(images_txt, psm=6)
        o2 = ocr_text_images(images_txt, psm=11)
        text, method, ocr_used = (o1 + "\n\n" + o2).strip(), "ocr_only_fallback", True

    try:
        table_map, table_evs = extract_percent_map_from_tables(pdf_bytes, page_indices_0=page_indices_0)
    except Exception:
        table_map, table_evs = {}, []

    row_map, row_evs = extract_percent_map_from_text_rows(text)

    images = render_pdf_pages_with_pdfium(pdf_bytes, page_indices_0, scale=settings.ocr_scale)

    ocr_data_norm = ocr_data_images_mode(images, psm=6, mode="thresh")
    ocr_data_inv = ocr_data_images_mode(images, psm=6, mode="invthresh")

    layout_map_n, layout_evs_n = extract_percent_map_from_ocr_layout(ocr_data_norm)
    layout_map_i, layout_evs_i = extract_percent_map_from_ocr_layout(ocr_data_inv)

    def _layout_score(m: Dict[str, Dict[str, Any]]) -> Tuple[int, int, int]:
        rows = len(m or {})
        has_d9 = 1 if ("delta9_pct" in m) else 0
        has_total = 1 if ("total_thc_pct" in m or "total_potential_thc_pct" in m) else 0
        return (rows, has_total, has_d9)

    if _layout_score(layout_map_i) > _layout_score(layout_map_n):
        layout_map, layout_evs = layout_map_i, layout_evs_i
        ocr_mode_used = "invthresh"
    else:
        layout_map, layout_evs = layout_map_n, layout_evs_n
        ocr_mode_used = "thresh"

    inline_evs = extract_inline_potency(text)

    percent_map = combine_percent_maps(table_map, layout_map, row_map)
    potency, conf = extract_potency_from_map(percent_map)

    for iev in inline_evs:
        if potency.get(iev.key) is None and iev.value_pct is not None:
            potency[iev.key] = float(iev.value_pct)
            conf[iev.key] = "high"

    scan_date = date.fromisoformat(settings.scan_date_iso)
    flagged, review_needed, payload = evaluate_client_flag_litigation(
        text=text,
        potency=potency,
        conf=conf,
        strict_dates_only=settings.strict_dates_only,
        scan_date=scan_date,
    )

    evidence = payload["details"].get("evidence") or {}
    evidence["pages_used_0"] = page_indices_0
    evidence["ocr_mode_used_for_layout"] = ocr_mode_used
    evidence["potency_evidence"] = [asdict(e) for e in (table_evs + layout_evs + row_evs + inline_evs)[:160]]

    return {
        "filename": name,
        "parsing_method": method,
        "ocr_used": ocr_used,
        "pages_scanned": len(page_indices_0),
        "page_indices_0": page_indices_0,
        "percent_map_count": len(percent_map),
        "percent_map_source": "tables+ocr_layout(loq_window)+ocr_rows+inline_fill",
        "potency": potency,
        "confidence": conf,
        "flagged": bool(flagged),
        "review_needed": bool(review_needed),
        "reasons_list": payload["reasons"],
        "details": payload["details"],
        "evidence": evidence,
    }


def scan_one_pdf(name: str, pdf_bytes: bytes, settings: ScanSettings) -> Dict[str, Any]:
    created_at = utc_now_iso()
    sha = sha256_bytes(pdf_bytes)

    total_pages = safe_pdf_page_count(pdf_bytes)
    if total_pages <= 0:
        raise RuntimeError("Unable to read PDF (page count = 0). Possibly encrypted/corrupt.")

    cap = min(settings.max_pages_cap, total_pages)

    p1_indices = list(range(min(settings.primary_pages, cap)))
    best = _run_pass(name, pdf_bytes, settings, p1_indices)
    deep_used = False
    full_used = False

    def needs_more(passd: Dict[str, Any]) -> bool:
        ev = passd.get("evidence") or {}
        strict_missing = any("STRICT DATE MODE: insufficient date evidence" in r for r in passd.get("reasons_list") or [])
        date_missing = (ev.get("expiration_evidence") is None) and (not (ev.get("best_analysis_completed_evidence") or ev.get("labeled_date_evidence")))
        potency_missing = all(v is None for v in (passd.get("potency") or {}).values())
        return strict_missing or date_missing or potency_missing

    if settings.enable_deep_scan and needs_more(best):
        try:
            page_texts = extract_text_pdfplumber_pages(pdf_bytes, max_pages=cap)
            rel = choose_relevant_pages_from_text(page_texts, max_pick=min(settings.relevant_page_pick, cap))
        except Exception:
            rel = list(range(min(settings.relevant_page_pick, cap)))

        rel = sorted(set(rel + p1_indices))
        p2 = _run_pass(name, pdf_bytes, settings, rel)
        if _score_pass(p2) > _score_pass(best):
            best = p2
            deep_used = True

    if settings.enable_full_fallback and needs_more(best):
        p3_indices = list(range(min(settings.deep_pages, cap)))
        p3 = _run_pass(name, pdf_bytes, settings, p3_indices)
        if _score_pass(p3) > _score_pass(best):
            best = p3
            full_used = True

    hemp_flag = False
    hemp_payload = {"reasons": [], "severity": "none", "delta9_pct": None, "thca_pct": None, "total_thc_pct": None}
    if settings.enable_hemp:
        hemp_flag, hemp_payload = evaluate_federal_hemp_from_potency(
            best["potency"],
            delta9_limit=float(settings.hemp_delta9_limit),
            total_limit=float(settings.hemp_total_limit),
            negligent_cutoff=float(settings.hemp_negligent_cutoff),
        )

    details = best["details"]
    evidence = best["evidence"]
    evidence["deep_scan_used"] = deep_used
    evidence["full_fallback_used"] = full_used
    evidence["page_count_cap"] = cap
    evidence["selected_pages_0"] = best.get("page_indices_0") or []

    return {
        "created_at_utc": created_at,
        "filename": name,
        "sha256": sha,
        "size_bytes": len(pdf_bytes),

        "parsing_method": best["parsing_method"],
        "ocr_used": best["ocr_used"],
        "max_pages_scanned": best["pages_scanned"],
        "deep_scan_used": deep_used,
        "full_fallback_used": full_used,

        "flagged": bool(best["flagged"]),
        "review_needed": bool(best["review_needed"]),
        "reasons": "; ".join(best["reasons_list"]),

        "test_date": details.get("test_date") or "",
        "expiration_date": details.get("expiration_date") or "",
        "effective_expiration_date": details.get("effective_expiration_date") or "",
        "earliest_date_found": details.get("earliest_date_found") or "",

        "expired_before_cutoff": details.get("expired_before_cutoff", False),
        "expired_as_of_scan": details.get("expired_as_of_scan", False),
        "has_early_date": details.get("has_early_date", False),

        "strict_dates_only": details.get("strict_dates_only", True),
        "used_labeled_dates": details.get("used_labeled_dates", False),
        "has_delta8": details.get("has_delta8", False),
        "has_delta9": details.get("has_delta9", False),

        "hemp_flag": bool(hemp_flag),
        "hemp_severity": hemp_payload.get("severity", "none"),
        "hemp_reasons": "; ".join(hemp_payload.get("reasons", [])),
        "hemp_delta9_pct": hemp_payload.get("delta9_pct"),
        "hemp_thca_pct": hemp_payload.get("thca_pct"),
        "hemp_total_thc_pct": hemp_payload.get("total_thc_pct"),

        "potency": best["potency"],
        "confidence": best["confidence"],
        "percent_map_count": best["percent_map_count"],
        "percent_map_source": best["percent_map_source"],

        "evidence": evidence,
    }


# ============================
# Parallel safety + ETA helpers
# ============================
WORKER_ENV_KEY = "LEAFLINE_WORKER_PROCESS"


def _is_worker_process() -> bool:
    return os.environ.get(WORKER_ENV_KEY, "0") == "1"


def _format_exc(e: BaseException) -> str:
    return "".join(traceback.format_exception(type(e), e, e.__traceback__))[-4000:]


def _fmt_duration(seconds: Optional[float]) -> str:
    if seconds is None:
        return "—"
    s = max(0, int(seconds + 0.5))
    m, s = divmod(s, 60)
    h, m = divmod(m, 60)
    if h:
        return f"{h}h {m}m {s}s"
    if m:
        return f"{m}m {s}s"
    return f"{s}s"


def _batch_timing(total: int, completed: int, batch_start: float) -> Dict[str, Optional[float]]:
    now = time.perf_counter()
    elapsed = now - batch_start
    if completed <= 0:
        return {"elapsed": elapsed, "sec_per_pdf": None, "eta": None}
    sec_per_pdf = elapsed / float(completed)
    remaining = max(0, total - completed)
    eta = sec_per_pdf * remaining
    return {"elapsed": elapsed, "sec_per_pdf": sec_per_pdf, "eta": eta}


# ============================
# Streamlit UI (main process only)
# ============================
def run_app() -> None:
    st.set_page_config(page_title=f"{APP_NAME} — Batch COA Scanner", layout="wide")
    init_db()

    st.title(APP_NAME)
    st.caption("Upload a ZIP of PDFs. Leafline scans each file, flags inconsistencies, and exports evidence for audit/litigation.")

    with st.sidebar:
        st.subheader("Scan depth (accuracy vs speed)")
        primary_pages = st.slider("Primary pages per PDF", 1, 20, 4)
        enable_deep_scan = st.toggle("Adaptive deep scan (recommended)", value=True)
        relevant_page_pick = st.slider("Relevant pages to OCR (deep scan)", 2, 20, 10)

        enable_full_fallback = st.toggle("Full fallback if still missing evidence", value=True)
        deep_pages = st.slider("Full fallback pages cap", 2, 30, 14)
        max_pages_cap = st.slider("Absolute max pages per PDF", 2, 60, 30)

        st.markdown("---")
        min_text_len = st.slider("OCR trigger threshold (chars)", 50, 2000, 250)
        ocr_scale = st.slider("OCR scale (higher = slower)", 1.5, 3.5, 2.7, 0.1)

        st.markdown("---")
        st.subheader("Litigation controls")
        strict_dates_only = st.toggle("STRICT: require explicit expiration or label-anchored dates", value=True)

        st.markdown("---")
        st.subheader("Parallel processing")
        workers = st.number_input("Workers", 1, max(1, (os.cpu_count() or 2)), 1, 1)

        st.markdown("---")
        st.subheader("Federal hemp checks")
        enable_hemp = st.toggle("Enable federal hemp checks", value=True)
        hemp_delta9_limit = st.number_input("Delta-9 THC limit (%)", value=float(HEMP_DELTA9_LIMIT), step=0.1, format="%.3f")
        hemp_total_limit = st.number_input("Total THC limit (%)", value=float(HEMP_TOTAL_LIMIT), step=0.1, format="%.3f")
        hemp_negligent_cutoff = st.number_input("Negligence threshold (%)", value=float(HEMP_TOTAL_NEGLIGENT_CUTOFF), step=0.1, format="%.3f")

        st.markdown("---")
        reviewer = st.text_input("Reviewer (optional)", value="")

    zip_up = st.file_uploader("Upload ZIP of PDFs", type=["zip"])
    run = st.button("Run batch scan", type="primary", disabled=(zip_up is None))

    if "batch_rows" not in st.session_state:
        st.session_state["batch_rows"] = []

    if zip_up and run:
        zbytes = zip_up.read()
        out_rows: List[Dict[str, Any]] = []

        settings = ScanSettings(
            primary_pages=int(primary_pages),
            deep_pages=int(deep_pages),
            max_pages_cap=int(max_pages_cap),
            enable_deep_scan=bool(enable_deep_scan),
            enable_full_fallback=bool(enable_full_fallback),
            relevant_page_pick=int(relevant_page_pick),
            min_text_len=int(min_text_len),
            ocr_scale=float(ocr_scale),
            strict_dates_only=bool(strict_dates_only),
            enable_hemp=bool(enable_hemp),
            hemp_delta9_limit=float(hemp_delta9_limit),
            hemp_total_limit=float(hemp_total_limit),
            hemp_negligent_cutoff=float(hemp_negligent_cutoff),
            scan_date_iso=date.today().isoformat(),
        )

        prog = st.progress(0.0)
        status = st.empty()
        batch_start = time.perf_counter()

        progress_text_fallback = st.empty()
        supports_progress_text = True

        def _set_progress(frac: float, text: str) -> None:
            nonlocal supports_progress_text
            if supports_progress_text:
                try:
                    prog.progress(frac, text=text)
                    return
                except TypeError:
                    supports_progress_text = False
                except Exception:
                    supports_progress_text = False
            prog.progress(frac)
            progress_text_fallback.caption(text)

        def make_error_row(name_: str, record_id_: str, created_at_: str, err: Exception) -> Dict[str, Any]:
            return {
                "record_id": record_id_,
                "created_at_utc": created_at_,
                "filename": name_,
                "sha256": "",
                "size_bytes": 0,
                "parsing_method": "error",
                "ocr_used": False,
                "max_pages_scanned": settings.primary_pages,
                "deep_scan_used": False,
                "full_fallback_used": False,
                "flagged": False,
                "review_needed": True,
                "reasons": f"ERROR: {err}",
                "test_date": "",
                "expiration_date": "",
                "effective_expiration_date": "",
                "earliest_date_found": "",
                "expired_before_cutoff": False,
                "expired_as_of_scan": False,
                "has_early_date": False,
                "strict_dates_only": settings.strict_dates_only,
                "used_labeled_dates": False,
                "has_delta8": False,
                "has_delta9": False,
                "hemp_flag": False,
                "hemp_severity": "none",
                "hemp_reasons": "",
                "hemp_delta9_pct": None,
                "hemp_thca_pct": None,
                "hemp_total_thc_pct": None,
                "potency": {},
                "confidence": {},
                "percent_map_count": 0,
                "percent_map_source": "none",
                "evidence": {"error": str(err), "traceback": _format_exc(err)},
                "ruleset_version": RULESET_VERSION,
                "fed_ruleset_version": FED_RULESET_VERSION,
                "app_version": APP_VERSION,
            }

        with zipfile.ZipFile(io.BytesIO(zbytes), "r") as z:
            names = [n for n in z.namelist() if n.lower().endswith(SUPPORTED_EXTS) and not n.endswith("/")]
            total = len(names)

            if total == 0:
                st.error("No PDFs found in the ZIP.")
            else:
                items = [(n, z.read(n)) for n in names]
                completed = 0
                _set_progress(0.0, "Starting batch…")

                def _progress_text(cur_name: str) -> str:
                    t = _batch_timing(total, completed, batch_start)
                    return (
                        f"{completed}/{total} done | "
                        f"Elapsed {_fmt_duration(t['elapsed'])} | "
                        f"Avg {_fmt_duration(t['sec_per_pdf'])}/pdf | "
                        f"ETA {_fmt_duration(t['eta'])} | "
                        f"Now: {cur_name}"
                    )

                if int(workers) == 1:
                    for name, b in items:
                        status.write(f"Scanning {completed + 1}/{total}: {name}")
                        _set_progress(completed / total, _progress_text(name))

                        record_id = str(uuid.uuid4())
                        created_at = utc_now_iso()
                        try:
                            row = scan_one_pdf(name, b, settings)
                            row["record_id"] = record_id
                            row["created_at_utc"] = created_at
                            row["ruleset_version"] = RULESET_VERSION
                            row["fed_ruleset_version"] = FED_RULESET_VERSION
                            row["app_version"] = APP_VERSION
                            out_rows.append(row)
                        except Exception as e:
                            out_rows.append(make_error_row(name, record_id, created_at, e))

                        completed += 1
                        _set_progress(completed / total, _progress_text(name))

                else:
                    prior = os.environ.get(WORKER_ENV_KEY)
                    os.environ[WORKER_ENV_KEY] = "1"
                    try:
                        ctx = mp.get_context("spawn")
                        with ProcessPoolExecutor(max_workers=int(workers), mp_context=ctx) as ex:
                            futs = {ex.submit(scan_one_pdf, name, b, settings): name for name, b in items}

                            for fut in as_completed(futs):
                                name = futs[fut]
                                status.write(f"Completed {completed + 1}/{total}: {name}")
                                _set_progress(completed / total, _progress_text(name))

                                record_id = str(uuid.uuid4())
                                created_at = utc_now_iso()
                                try:
                                    row = fut.result()
                                    row["record_id"] = record_id
                                    row["created_at_utc"] = created_at
                                    row["ruleset_version"] = RULESET_VERSION
                                    row["fed_ruleset_version"] = FED_RULESET_VERSION
                                    row["app_version"] = APP_VERSION
                                    out_rows.append(row)
                                except Exception as e:
                                    out_rows.append(make_error_row(name, record_id, created_at, e))

                                completed += 1
                                _set_progress(completed / total, _progress_text(name))
                    finally:
                        if prior is None:
                            os.environ.pop(WORKER_ENV_KEY, None)
                        else:
                            os.environ[WORKER_ENV_KEY] = prior

                for row in out_rows:
                    try:
                        db_insert_event(row["record_id"], "EVALUATED", {
                            "filename": row["filename"],
                            "sha256": row.get("sha256"),
                            "parsing_method": row.get("parsing_method"),
                            "ocr_used": row.get("ocr_used"),
                            "flagged": row.get("flagged"),
                            "review_needed": row.get("review_needed"),
                            "reasons": row.get("reasons"),
                            "potency": row.get("potency"),
                            "confidence": row.get("confidence"),
                            "evidence": row.get("evidence"),
                            "ruleset_version": RULESET_VERSION,
                            "fed_ruleset_version": FED_RULESET_VERSION,
                            "app_version": APP_VERSION,
                        })

                        db_insert_record({
                            "record_id": row["record_id"],
                            "created_at_utc": row["created_at_utc"],
                            "reviewer": reviewer or None,
                            "source_filename": row["filename"],
                            "source_sha256": row.get("sha256", ""),
                            "source_size_bytes": row.get("size_bytes", 0),
                            "ruleset_version": RULESET_VERSION,
                            "fed_ruleset_version": FED_RULESET_VERSION,
                            "app_version": APP_VERSION,
                            "parsing_method": row.get("parsing_method", ""),
                            "max_pages_scanned": int(row.get("max_pages_scanned", 0)),
                            "ocr_used": bool(row.get("ocr_used", False)),
                            "flagged": bool(row.get("flagged", False)),
                            "review_needed": bool(row.get("review_needed", False)),
                            "reasons": row.get("reasons", ""),
                            "expiration_date": row.get("expiration_date") or None,
                            "effective_expiration_date": row.get("effective_expiration_date") or None,
                            "test_date": row.get("test_date") or None,
                            "earliest_date_found": row.get("earliest_date_found") or None,
                            "expired_before_cutoff": bool(row.get("expired_before_cutoff", False)),
                            "expired_as_of_scan": bool(row.get("expired_as_of_scan", False)),
                            "has_early_date": bool(row.get("has_early_date", False)),
                            "hemp_flag": bool(row.get("hemp_flag", False)),
                            "hemp_severity": row.get("hemp_severity", "none"),
                            "hemp_reasons": row.get("hemp_reasons", ""),
                            "hemp_delta9_pct": row.get("hemp_delta9_pct"),
                            "hemp_thca_pct": row.get("hemp_thca_pct"),
                            "hemp_total_thc_pct": row.get("hemp_total_thc_pct"),
                            "potency_json": json.dumps(row.get("potency") or {}, ensure_ascii=False),
                            "evidence_json": json.dumps(row.get("evidence") or {}, ensure_ascii=False),
                            "percent_map_count": int(row.get("percent_map_count", 0)),
                        })
                    except Exception as e:
                        db_insert_event(row["record_id"], "DB_ERROR", {"filename": row["filename"], "error": str(e), "traceback": _format_exc(e)})

        st.session_state["batch_rows"] = out_rows
        t_done = _batch_timing(total, total, batch_start)
        _set_progress(1.0, f"Done | Elapsed {_fmt_duration(t_done['elapsed'])} | Avg {_fmt_duration(t_done['sec_per_pdf'])}/pdf")

    rows = st.session_state.get("batch_rows", [])
    if rows:
        df = pd.DataFrame([{
            "record_id": r["record_id"],
            "created_at_utc": r["created_at_utc"],
            "filename": r["filename"],
            "flagged": r["flagged"],
            "review_needed": r.get("review_needed", False),
            "hemp_flagged": r.get("hemp_flag", False),
            "hemp_severity": r.get("hemp_severity", ""),
            "deep_scan_used": r.get("deep_scan_used", False),
            "full_fallback_used": r.get("full_fallback_used", False),
            "test_date": r.get("test_date", ""),
            "effective_expiration_date": r.get("effective_expiration_date", ""),
            "pot_total_thc_pct": (r.get("potency") or {}).get("total_thc_pct"),
            "pot_delta9_pct": (r.get("potency") or {}).get("delta9_pct"),
            "pot_thca_pct": (r.get("potency") or {}).get("thca_pct"),
            "pot_delta8_pct": (r.get("potency") or {}).get("delta8_pct"),
            "percent_map_count": r.get("percent_map_count", 0),
            "ocr_used": r.get("ocr_used", False),
            "pages_scanned": r.get("max_pages_scanned", 0),
            "reasons": r.get("reasons", ""),
            "sha256": r.get("sha256", ""),
        } for r in rows])

        total = len(df)
        c1, c2, c3, c4, c5, c6 = st.columns([1, 1, 1, 1, 1, 1])
        c1.metric("Total scanned", total)
        c2.metric("Client flagged", int(df["flagged"].sum()))
        c3.metric("Review-needed", int(df["review_needed"].sum()))
        c4.metric("Hemp-flagged", int(df["hemp_flagged"].sum()))
        c5.metric("Deep scan used", int(df["deep_scan_used"].sum()))
        c6.metric("Full fallback used", int(df["full_fallback_used"].sum()))

        st.divider()
        st.subheader("Batch results")
        st.dataframe(df, use_container_width=True)

        st.subheader("Export")
        st.download_button(
            "Download CSV",
            data=df.to_csv(index=False).encode("utf-8"),
            file_name=f"Leafline_Batch_{datetime.now(timezone.utc).strftime('%Y%m%d_%H%M%S')}Z.csv",
            mime="text/csv",
        )

        batch_pdf = generate_batch_pdf_report(rows)
        st.download_button(
            "Download Batch PDF Report",
            data=batch_pdf,
            file_name=f"Leafline_Batch_Report_{datetime.now(timezone.utc).strftime('%Y%m%d_%H%M%S')}Z.pdf",
            mime="application/pdf",
        )

        evidence_bundle = [{
            "record_id": r["record_id"],
            "filename": r["filename"],
            "sha256": r.get("sha256"),
            "flagged": r.get("flagged"),
            "review_needed": r.get("review_needed"),
            "reasons": r.get("reasons"),
            "potency": r.get("potency"),
            "confidence": r.get("confidence"),
            "evidence": r.get("evidence"),
        } for r in rows]
        st.download_button(
            "Download Evidence Bundle (JSON)",
            data=json.dumps(evidence_bundle, ensure_ascii=False, indent=2).encode("utf-8"),
            file_name=f"Leafline_Evidence_{datetime.now(timezone.utc).strftime('%Y%m%d_%H%M%S')}Z.json",
            mime="application/json",
        )
    else:
        st.info("Upload a ZIP of PDFs to run a batch scan.")


if not _is_worker_process():
    run_app()
