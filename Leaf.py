# app.py
"""
Leafline — Batch COA Scanner (litigation-grade)
- Conservative potency extraction with unit handling.
- Strict date logic + "effective expiration" = test date + 365 days (common practice) when explicit expiration missing.
- Evidence-first exports.
- Optional parallel scanning; DB writes remain in main process.
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
from dataclasses import dataclass, asdict
from datetime import datetime, date, timezone, timedelta
from typing import List, Dict, Optional, Tuple, Any
from concurrent.futures import ProcessPoolExecutor, as_completed

import streamlit as st
import pandas as pd
import pdfplumber
from dateutil import parser as dateparser

from PIL import Image
import pypdfium2 as pdfium
import pytesseract

from reportlab.lib.pagesizes import letter
from reportlab.lib.units import inch
from reportlab.pdfgen import canvas

try:
    mp.set_start_method("spawn", force=True)
except RuntimeError:
    pass


# ============================
# App constants
# ============================
APP_NAME = "Leafline"
APP_VERSION = "3.0.0"
DB_PATH = "leafline_audit.db"
SUPPORTED_EXTS = (".pdf",)

# ============================
# Client-required flag logic
# ============================
EXPIRY_CUTOFF = date(2021, 11, 24)
EARLY_YEAR_CUTOFF = 2020
CLIENT_THC_THRESHOLD = 0.3  # percent
COA_VALIDITY_DAYS = 365     # common practice: COA effectively "expires" 365 days after test/analysis date

DELTA8_TERMS = [
    r"delta\s*[-]?\s*8", r"\bdelta8\b", r"Δ\s*8", r"\bΔ8\b", r"\bD8\b", r"\bd8[-\s]*thc\b"
]
DELTA9_TERMS = [
    r"delta\s*[-]?\s*9", r"\bdelta9\b", r"Δ\s*9", r"\bΔ9\b", r"\bD9\b", r"\bd9[-\s]*thc\b"
]
THC_CONTEXT_TERMS = [r"\bTHC\b", r"tetrahydrocannabinol", r"\bcannabinoid\b", r"\bpotency\b"]

RULESET_VERSION = "client_flag_v8_365day_expiry_summary_parallel"
FED_RULESET_VERSION = "federal_hemp_v1"

# ============================
# Federal hemp thresholds
# ============================
HEMP_DELTA9_LIMIT = 0.3
HEMP_TOTAL_LIMIT = 0.3
HEMP_TOTAL_NEGLIGENT_CUTOFF = 1.0
THCA_DECARB_FACTOR = 0.877


# ============================
# Utilities
# ============================
def utc_now_iso() -> str:
    return datetime.now(timezone.utc).isoformat(timespec="seconds")


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def _norm(s: str) -> str:
    return re.sub(r"\s+", " ", (s or "").strip()).lower()


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
    if re.fullmatch(r"nd|n\.d\.|not detected", s, flags=re.IGNORECASE):
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


# ============================
# Evidence structures
# ============================
@dataclass(frozen=True)
class PotencyEvidence:
    key: str
    value_pct: Optional[float]
    source: str  # "table" | "ocr_row" | "inline_text"
    confidence: str  # "high" | "medium" | "low" | "none" | "computed"
    page: Optional[int] = None
    raw_name: Optional[str] = None
    raw_value: Optional[str] = None
    snippet: Optional[str] = None
    notes: Optional[str] = None


@dataclass(frozen=True)
class DateEvidence:
    kind: str  # "expiration" | "labeled_report_date" | "derived_expiration_365"
    value: str  # ISO date
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
    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
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
# Text + OCR extraction
# ============================
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
    text = extract_text_pdfplumber(pdf_bytes, max_pages=max_pages)
    if len(text) >= min_text_len:
        return text, "pdf_text", False

    images = render_pdf_pages_with_pdfium(pdf_bytes, max_pages=max_pages, scale=ocr_scale)
    ocr_text = ocr_images(images)
    combined = (text + "\n\n" + ocr_text).strip()
    return combined, "hybrid_text+ocr", True


# ============================
# Dates (strict labeled + expiration + derived 365)
# ============================
MONTH_NAME_RE = r"(?:jan(?:uary)?|feb(?:ruary)?|mar(?:ch)?|apr(?:il)?|may|jun(?:e)?|jul(?:y)?|aug(?:ust)?|sep(?:t(?:ember)?)?|oct(?:ober)?|nov(?:ember)?|dec(?:ember)?)"

DATE_LABEL_PATTERNS = [
    r"\breport\s*date\b",
    r"\bdate\s*of\s*report\b",
    r"\bcoa\s*date\b",
    r"\bissued\s*date\b",
    r"\bdate\s*issued\b",
    r"\bdate\s*reported\b",
    r"\breported\s*on\b",
    r"\btest\s*date\b",
    r"\bdate\s*tested\b",
    r"\bdate\s*of\s*test\b",
    r"\bdate\s*of\s*analysis\b",
    r"\banalysis\s*date\b",
    r"\bdate\s*analyzed\b",
    r"\bsample\s*date\b",
    r"\bcollection\s*date\b",
    r"\bdate\s*received\b",
    r"\breceived\s*date\b",
    r"\brep[o0]rt\s*date\b",
    r"\bte[s5]t\s*date\b",
]


def extract_expiration_date(text: str) -> Tuple[Optional[date], Optional[DateEvidence]]:
    if not text:
        return None, None

    exp_line_patterns = [
        rf"(?:expiration\s*date|exp\s*date|expires?|expir\w*)\s*[:\-]?\s*(\d{{1,2}}[/-]\d{{1,2}}[/-]\d{{2,4}})",
        rf"(?:expiration\s*date|exp\s*date|expires?|expir\w*)\s*[:\-]?\s*(\d{{4}}-\d{{2}}-\d{{2}})",
        rf"(?:expiration\s*date|exp\s*date|expires?|expir\w*)\s*[:\-]?\s*({MONTH_NAME_RE}\s+\d{{1,2}}(?:,)?\s+\d{{4}})",
        rf"(?:expiration\s*date|exp\s*date|expires?|expir\w*)\s*[:\-]?\s*(\d{{1,2}}\s+{MONTH_NAME_RE}(?:,)?\s+\d{{4}})",
    ]
    for pat in exp_line_patterns:
        m = re.search(pat, text, flags=re.IGNORECASE)
        if not m:
            continue
        tok = m.group(1)
        d = safe_parse_date(tok)
        if d:
            snippet = (m.group(0) or "")[:240]
            return d, DateEvidence(kind="expiration", value=d.isoformat(), source="regex", snippet=snippet)
    return None, None


def extract_labeled_report_dates(text: str) -> List[Tuple[date, DateEvidence]]:
    if not text:
        return []
    label_re = re.compile("|".join(DATE_LABEL_PATTERNS), re.IGNORECASE)

    date_token_res = [
        r"(\d{1,2}[/-]\d{1,2}[/-]\d{2,4})",
        r"(\d{4}-\d{2}-\d{2})",
        rf"({MONTH_NAME_RE}\s+\d{{1,2}}(?:,)?\s+\d{{4}})",
        rf"(\d{{1,2}}\s+{MONTH_NAME_RE}(?:,)?\s+\d{{4}})",
    ]

    out: List[Tuple[date, DateEvidence]] = []
    for ln in (ln.strip() for ln in text.splitlines() if ln.strip()):
        if not label_re.search(ln):
            continue
        for dt_re in date_token_res:
            m = re.search(dt_re, ln, flags=re.IGNORECASE)
            if not m:
                continue
            d = safe_parse_date(m.group(1))
            if not d:
                continue
            out.append((d, DateEvidence(kind="labeled_report_date", value=d.isoformat(), source="regex", snippet=ln[:240])))
            break

    uniq: Dict[str, Tuple[date, DateEvidence]] = {}
    for d, ev in out:
        uniq[d.isoformat()] = (d, ev)
    return sorted(list(uniq.values()), key=lambda x: x[0])


def compute_effective_expiration(
    exp_date: Optional[date],
    test_date: Optional[date],
) -> Tuple[Optional[date], Optional[DateEvidence]]:
    if exp_date:
        return exp_date, None
    if test_date:
        eff = test_date + timedelta(days=COA_VALIDITY_DAYS)
        ev = DateEvidence(
            kind="derived_expiration_365",
            value=eff.isoformat(),
            source="derived",
            snippet=f"Derived: test_date({test_date.isoformat()}) + {COA_VALIDITY_DAYS} days",
        )
        return eff, ev
    return None, None


# ============================
# Potency extraction (same as before, included for completeness)
# ============================
ANALYTE_KEYS: Dict[str, List[str]] = {
    "delta8_pct": [
        r"\bdelta\s*[-]?\s*8\b", r"\bdelta8\b", r"\bΔ\s*8\b", r"\bΔ8\b",
        r"\bD8\b", r"\bd8[-\s]*thc\b", r"delta\s*8\s*thc",
    ],
    "delta9_pct": [
        r"\bdelta\s*[-]?\s*9\b", r"\bdelta9\b", r"\bΔ\s*9\b", r"\bΔ9\b",
        r"\bD9\b", r"\bd9[-\s]*thc\b", r"delta\s*9\s*thc",
    ],
    "thca_pct": [
        r"\bthca\b", r"thc[-\s]*a\b", r"tetrahydrocannabinolic",
    ],
    "total_thc_pct": [
        r"\btotal\s*thc\b", r"\bthc\s*total\b", r"\bmax\s*active\s*thc\b", r"\btotal\s*active\s*thc\b",
    ],
    "total_potential_thc_pct": [
        r"\btotal\s*potential\s*thc\b", r"\bpotential\s*thc\b",
    ],
}

_ND_RE = re.compile(r"\bnd\b|n\.d\.|not\s+detected", re.IGNORECASE)
_NUM_RE = re.compile(r"(?<!\w)(\d+(?:\.\d+)?)(?!\w)")
_HAS_PERCENT = re.compile(r"%")
_HAS_MG_G = re.compile(r"\bmg\s*/?\s*g\b|\bmg\s+g\b", re.IGNORECASE)
_HAS_MG_KG = re.compile(r"\bmg\s*/?\s*kg\b", re.IGNORECASE)
_HAS_PPM = re.compile(r"\bppm\b", re.IGNORECASE)


def _match_analyte_key(s: str) -> Optional[str]:
    for k, pats in ANALYTE_KEYS.items():
        for p in pats:
            if re.search(p, s, flags=re.IGNORECASE):
                return k
    return None


def _normalize_to_percent(raw: float, line: str) -> Tuple[Optional[float], str, str]:
    if raw < 0:
        return None, "low", "negative_value"

    if _HAS_PERCENT.search(line):
        if raw <= 100.0:
            return raw, "high", "explicit_percent"
        return None, "low", "explicit_percent_but_out_of_range"

    if _HAS_MG_G.search(line):
        pct = raw / 10.0
        if pct <= 100.0:
            return pct, "high", "unit_mg_per_g_div10"
        return None, "low", "unit_mg_per_g_div10_out_of_range"

    if _HAS_MG_KG.search(line) or _HAS_PPM.search(line):
        pct = raw / 10000.0
        if pct <= 100.0:
            return pct, "high", "unit_ppm_or_mg_per_kg_div10000"
        return None, "low", "unit_ppm_or_mg_per_kg_div10000_out_of_range"

    if raw > 100.0:
        return None, "low", "no_unit_raw_gt_100_rejected"

    if 20.0 < raw <= 100.0:
        pct = raw / 10.0
        return pct, "medium", "no_unit_assumed_mg_per_g_div10"

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


def extract_percent_map_from_tables(pdf_bytes: bytes, max_pages: int) -> Tuple[Dict[str, Dict[str, Any]], List[PotencyEvidence]]:
    out: Dict[str, Dict[str, Any]] = {}
    evs: List[PotencyEvidence] = []

    with pdfplumber.open(io.BytesIO(pdf_bytes)) as pdf:
        for page_idx, page in enumerate(pdf.pages[:max_pages], start=1):
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
                for i, h in enumerate(header_norm):
                    if h in ["%", "percent", "% w/w", "%ww", "percent w/w", "percent (w/w)"] or ("%" in h and "loq" not in h):
                        pct_idx = i
                        break
                if pct_idx is None:
                    continue

                name_idx = None
                for i, h in enumerate(header_norm):
                    if any(k in h for k in ["analyte", "compound", "cannabinoid", "name"]):
                        name_idx = i
                        break
                if name_idx is None:
                    name_idx = 0

                for row in table[1:]:
                    if not row or len(row) <= max(pct_idx, name_idx):
                        continue
                    raw_name = (row[name_idx] or "").strip()
                    if not raw_name:
                        continue

                    key = _match_analyte_key(raw_name)
                    if not key:
                        continue

                    raw_val_cell = row[pct_idx]
                    raw_val = _parse_float_or_nd(raw_val_cell)
                    if raw_val is None:
                        continue

                    row_join = " ".join([str(x) for x in row if x is not None])
                    pct, conf, notes = _normalize_to_percent(float(raw_val), row_join)

                    ev = PotencyEvidence(
                        key=key,
                        value_pct=pct,
                        source="table",
                        confidence=conf,
                        page=page_idx,
                        raw_name=raw_name[:120],
                        raw_value=str(raw_val_cell)[:80],
                        snippet=row_join[:240],
                        notes=notes,
                    )
                    evs.append(ev)

                    if pct is None:
                        continue

                    prev = out.get(key, {}).get("pct")
                    if prev is None or pct > float(prev):
                        out[key] = {
                            "pct": pct,
                            "raw_name": raw_name,
                            "raw_value": str(raw_val_cell),
                            "source": "table",
                            "page": page_idx,
                            "snippet": row_join[:240],
                            "confidence": conf,
                            "notes": notes,
                        }

    return out, evs


def extract_percent_map_from_text(text: str) -> Tuple[Dict[str, Dict[str, Any]], List[PotencyEvidence]]:
    out: Dict[str, Dict[str, Any]] = {}
    evs: List[PotencyEvidence] = []

    if not text:
        return out, evs

    for ln in (ln.strip() for ln in text.splitlines() if ln.strip()):
        if len(ln) < 6:
            continue
        if re.search(r"prepared\s+for|final\s+authorization|remarks|page\s+\d+\s+of|\bcoa\b", ln, re.I):
            continue

        key = _match_analyte_key(ln)
        if not key:
            continue

        pct, conf, notes, raw_value = _extract_row_value(ln)
        ev = PotencyEvidence(
            key=key,
            value_pct=pct,
            source="ocr_row",
            confidence=conf,
            page=None,
            raw_name=key,
            raw_value=raw_value[:80],
            snippet=ln[:240],
            notes=notes,
        )
        evs.append(ev)

        if pct is None:
            continue

        prev = out.get(key, {}).get("pct")
        if prev is None or pct > float(prev):
            out[key] = {
                "pct": pct,
                "raw_name": key,
                "raw_value": raw_value,
                "source": "ocr_row",
                "page": None,
                "snippet": ln[:240],
                "confidence": conf,
                "notes": notes,
            }

    return out, evs


INLINE_POTENCY_PATTERNS = {
    "delta8_pct": [
        r"(?:delta\s*[-]?\s*8|Δ\s*8|Δ8|d8)\s*(?:thc)?\s*[:\-]?\s*(nd|n\.d\.|not detected|\d+(?:\.\d+)?)\s*%",
    ],
    "delta9_pct": [
        r"(?:delta\s*[-]?\s*9|Δ\s*9|Δ9|d9)\s*(?:thc)?\s*[:\-]?\s*(nd|n\.d\.|not detected|\d+(?:\.\d+)?)\s*%",
    ],
    "thca_pct": [
        r"\bthc[\s\-]*a\b\s*[:\-]?\s*(nd|n\.d\.|not detected|\d+(?:\.\d+)?)\s*%",
        r"\btetrahydrocannabinolic\b.*?\s*(nd|n\.d\.|not detected|\d+(?:\.\d+)?)\s*%",
    ],
    "total_thc_pct": [
        r"\btotal\s*thc\b\s*[:\-]?\s*(nd|n\.d\.|not detected|\d+(?:\.\d+)?)\s*%",
    ],
    "total_potential_thc_pct": [
        r"\btotal\s*potential\s*thc\b\s*[:\-]?\s*(nd|n\.d\.|not detected|\d+(?:\.\d+)?)\s*%",
    ],
}


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
                key=key,
                value_pct=best[0],
                source="inline_text",
                confidence="high",
                page=None,
                raw_name=key,
                raw_value=str(best[0]),
                snippet=best[1],
                notes="explicit_percent_inline",
            ))
    return out


def combine_percent_maps(primary: Dict[str, Dict[str, Any]], fallback: Dict[str, Dict[str, Any]]) -> Dict[str, Dict[str, Any]]:
    out = dict(primary)
    for k, v in fallback.items():
        if k not in out:
            out[k] = v
    return out


def extract_potency_from_map(percent_map: Dict[str, Dict[str, Any]]) -> Tuple[Dict[str, Optional[float]], Dict[str, str]]:
    potency: Dict[str, Optional[float]] = {}
    conf: Dict[str, str] = {}
    for k in ["delta8_pct", "delta9_pct", "thca_pct", "total_thc_pct", "total_potential_thc_pct"]:
        if k in percent_map:
            potency[k] = float(percent_map[k]["pct"])
            conf[k] = str(percent_map[k].get("confidence") or "unknown")
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

        if c in ("high", "computed"):
            evidence.append(f"{k}={float(v):.3f}% (conf={c})")
            if float(v) > threshold:
                return True, evidence, review_needed
        else:
            evidence.append(f"{k}={float(v):.3f}% (conf={c})")
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

    hemp_flag = severity in ("breach", "elevated")
    return hemp_flag, {
        "reasons": reasons,
        "severity": severity,
        "delta9_pct": d9,
        "thca_pct": thca,
        "total_thc_pct": total,
    }


# ============================
# Client flag (365-day expiry logic added)
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
    labeled_dates = extract_labeled_report_dates(text)

    test_date: Optional[date] = labeled_dates[0][0] if labeled_dates else None

    eff_exp_date, derived_ev = compute_effective_expiration(exp_date, test_date)

    expired_before_cutoff = bool(eff_exp_date and eff_exp_date < EXPIRY_CUTOFF)
    expired_as_of_scan = bool(eff_exp_date and eff_exp_date < scan_date)

    early_labeled = [d for d, _ in labeled_dates if d.year <= EARLY_YEAR_CUTOFF]
    has_early_date = bool(early_labeled)

    if strict_dates_only and (not exp_date) and (not labeled_dates):
        reasons.append("STRICT DATE MODE: insufficient date evidence (no explicit expiration and no labeled test/report date)")
        date_condition = False
        date_review = True
    else:
        date_condition = expired_before_cutoff or has_early_date
        date_review = False if (exp_date or labeled_dates) else True

    reasons.append("Delta 8/9 detected" if has_delta else "No Delta 8/9 detected")
    reasons.append("THC context detected" if has_thc_context else "No THC context detected")
    reasons.append(f"THC above {CLIENT_THC_THRESHOLD}% detected" if thc_over else f"No THC above {CLIENT_THC_THRESHOLD}% detected")

    if exp_date:
        reasons.append(f"Explicit expiration date found: {exp_date.isoformat()}")
    else:
        reasons.append("No explicit expiration date found")

    if test_date:
        reasons.append(f"Test/Report date found: {test_date.isoformat()}")
    else:
        reasons.append("No labeled test/report date found")

    if eff_exp_date:
        if exp_date:
            reasons.append(f"Effective expiration date: {eff_exp_date.isoformat()} (explicit)")
        else:
            reasons.append(f"Effective expiration date: {eff_exp_date.isoformat()} (derived test_date + {COA_VALIDITY_DAYS} days)")
    else:
        reasons.append("No effective expiration date available")

    if expired_before_cutoff:
        reasons.append(f"Expired before cutoff {EXPIRY_CUTOFF.isoformat()} (effective expiration)")
    if expired_as_of_scan:
        reasons.append(f"Expired as of scan date {scan_date.isoformat()} (effective expiration)")

    if labeled_dates:
        reasons.append("Used labeled report/test dates")
        if has_early_date:
            reasons.append(f"Contains labeled date in {EARLY_YEAR_CUTOFF} or earlier (e.g., {early_labeled[0].isoformat()})")
    else:
        reasons.append("No labeled report/test dates found")

    if not date_condition:
        reasons.append(
            f"Date condition not met (needs expired-before-cutoff using effective expiration OR labeled date in {EARLY_YEAR_CUTOFF} or earlier)"
        )

    flagged = bool(has_delta and has_thc_context and thc_over and date_condition)
    review_needed = bool(potency_review or date_review)

    earliest_found = ""
    if early_labeled:
        earliest_found = early_labeled[0].isoformat()
    elif labeled_dates:
        earliest_found = labeled_dates[0][0].isoformat()

    evidence["thc_over_evidence"] = thc_ev
    evidence["expiration_evidence"] = asdict(exp_ev) if exp_ev else None
    evidence["derived_expiration_evidence"] = asdict(derived_ev) if derived_ev else None
    evidence["labeled_date_evidence"] = [asdict(ev) for _, ev in labeled_dates[:10]]
    evidence["potency_confidence"] = conf

    details = {
        "has_delta8": has_delta8,
        "has_delta9": has_delta9,

        "scan_date": scan_date.isoformat(),
        "test_date": test_date.isoformat() if test_date else "",
        "expiration_date": exp_date.isoformat() if exp_date else "",
        "effective_expiration_date": eff_exp_date.isoformat() if eff_exp_date else "",

        "earliest_date_found": earliest_found,
        "expired_before_cutoff": expired_before_cutoff,
        "expired_as_of_scan": expired_as_of_scan,
        "has_early_date": has_early_date,

        "strict_dates_only": strict_dates_only,
        "used_labeled_dates": bool(labeled_dates),

        "potency": potency,
        "evidence": evidence,
    }
    return flagged, review_needed, {"reasons": reasons, "details": details}


# ============================
# PDF report export (adds % summary + hemp breakdown)
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


def _pct(part: int, total: int) -> str:
    if total <= 0:
        return "0.0%"
    return f"{(part / total) * 100.0:.1f}%"


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

    hemp_breach = sum(1 for r in rows if (r.get("hemp_severity") == "breach"))
    hemp_elevated = sum(1 for r in rows if (r.get("hemp_severity") == "elevated"))
    hemp_unknown = sum(1 for r in rows if (r.get("hemp_severity") == "unknown"))

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
    y -= 14

    c.drawString(
        x, y,
        f"Hemp severities: breach={hemp_breach} ({_pct(hemp_breach, total)}), "
        f"elevated={hemp_elevated} ({_pct(hemp_elevated, total)}), "
        f"unknown={hemp_unknown} ({_pct(hemp_unknown, total)})"
    )
    y -= 18

    c.setFont("Helvetica-Bold", 11)
    c.drawString(x, y, "Client Flag Logic")
    y -= 14
    c.setFont("Helvetica", 10)
    y = wrap_text(
        c,
        f"Flag if: (Delta 8 or Delta 9) AND (THC > {CLIENT_THC_THRESHOLD}%) AND "
        f"(Expired before {EXPIRY_CUTOFF.isoformat()} using EFFECTIVE expiration OR labeled date in {EARLY_YEAR_CUTOFF} or earlier).",
        x, y, max_w
    )
    y = wrap_text(
        c,
        f"Effective expiration = explicit expiration date OR (test/report date + {COA_VALIDITY_DAYS} days).",
        x, y, max_w
    )
    y -= 10

    c.setFont("Helvetica-Bold", 12)
    c.drawString(x, y, "Flagged / Review-needed / Hemp-flagged (details)")
    y -= 16

    focus_rows = [r for r in rows if (r.get("flagged") is True or r.get("review_needed") is True or r.get("hemp_flag") is True)]
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
            f"Extraction: {r.get('parsing_method', '')} (OCR: {bool(r.get('ocr_used'))}, pages: {r.get('max_pages_scanned')})",
            x, y, max_w, size=9, leading=11
        )
        y = wrap_text(
            c,
            f"Client flagged: {bool(r.get('flagged'))} | Review-needed: {bool(r.get('review_needed'))} | Hemp flagged: {bool(r.get('hemp_flag'))}",
            x, y, max_w, size=9, leading=11
        )

        if r.get("test_date"):
            y = wrap_text(c, f"Test/Report date: {r['test_date']}", x, y, max_w, size=9, leading=11)
        if r.get("expiration_date"):
            y = wrap_text(c, f"Explicit expiration date: {r['expiration_date']}", x, y, max_w, size=9, leading=11)
        if r.get("effective_expiration_date"):
            y = wrap_text(c, f"Effective expiration date: {r['effective_expiration_date']}", x, y, max_w, size=9, leading=11)

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
        thc_over_ev = ev.get("thc_over_evidence") or []
        if thc_over_ev:
            y = wrap_text(c, "THC evidence:", x, y, max_w, size=9, leading=11)
            for line in thc_over_ev[:6]:
                y = wrap_text(c, f"- {line}", x + 12, y, max_w - 12, size=9, leading=11)

        y = wrap_text(c, f"Reasons: {r.get('reasons', '')}", x, y, max_w, size=9, leading=11)
        y -= 8

    c.save()
    return buf.getvalue()


# ============================
# Parallel worker
# ============================
@dataclass(frozen=True)
class ScanSettings:
    max_pages: int
    min_text_len: int
    ocr_scale: float
    strict_dates_only: bool
    enable_hemp: bool
    hemp_delta9_limit: float
    hemp_total_limit: float
    hemp_negligent_cutoff: float
    scan_date_iso: str  # used for "expired as of scan date"


def scan_one_pdf(name: str, pdf_bytes: bytes, settings: ScanSettings) -> Dict[str, Any]:
    created_at = utc_now_iso()
    sha = sha256_bytes(pdf_bytes)
    scan_date = date.fromisoformat(settings.scan_date_iso)

    text, method, ocr_used = extract_text_hybrid(
        pdf_bytes,
        max_pages=settings.max_pages,
        min_text_len=settings.min_text_len,
        ocr_scale=settings.ocr_scale,
    )

    table_map, table_evs = extract_percent_map_from_tables(pdf_bytes, max_pages=settings.max_pages)
    ocr_map, ocr_evs = extract_percent_map_from_text(text)
    percent_map = combine_percent_maps(table_map, ocr_map)

    inline_evs = extract_inline_potency(text)

    potency, conf = extract_potency_from_map(percent_map)

    for iev in inline_evs:
        if potency.get(iev.key) is None and iev.value_pct is not None:
            potency[iev.key] = float(iev.value_pct)
            conf[iev.key] = "high"

    flagged, review_needed, payload = evaluate_client_flag_litigation(
        text=text,
        potency=potency,
        conf=conf,
        strict_dates_only=settings.strict_dates_only,
        scan_date=scan_date,
    )

    reasons_list = payload["reasons"]
    details = payload["details"]
    evidence = details.get("evidence") or {}
    evidence["potency_evidence"] = [asdict(e) for e in (table_evs + ocr_evs + inline_evs)[:60]]

    hemp_flag = False
    hemp_payload = {"reasons": [], "severity": "none", "delta9_pct": None, "thca_pct": None, "total_thc_pct": None}
    if settings.enable_hemp:
        hemp_flag, hemp_payload = evaluate_federal_hemp_from_potency(
            potency,
            delta9_limit=float(settings.hemp_delta9_limit),
            total_limit=float(settings.hemp_total_limit),
            negligent_cutoff=float(settings.hemp_negligent_cutoff),
        )

    return {
        "created_at_utc": created_at,
        "filename": name,
        "sha256": sha,
        "size_bytes": len(pdf_bytes),

        "parsing_method": method,
        "ocr_used": ocr_used,
        "max_pages_scanned": settings.max_pages,

        "flagged": bool(flagged),
        "review_needed": bool(review_needed),
        "reasons": "; ".join(reasons_list),

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

        "potency": potency,
        "confidence": conf,
        "percent_map_count": len(percent_map),
        "percent_map_source": "canonical(table+ocr)+inline_fill",

        "evidence": evidence,
    }


# ============================
# Streamlit UI
# ============================
st.set_page_config(page_title=f"{APP_NAME} — Batch COA Scanner", layout="wide")
init_db()

st.title(APP_NAME)
st.caption("Upload a ZIP of PDFs. Leafline scans each file, flags matches, and exports evidence for audit/litigation.")

with st.sidebar:
    st.subheader("Scan settings")
    max_pages = st.slider("Pages to scan per PDF", 1, 30, 8)
    min_text_len = st.slider("OCR trigger threshold (characters)", 50, 800, 200)
    ocr_scale = st.slider("OCR quality (higher = slower)", 1.5, 3.0, 2.2, 0.1)

    st.markdown("---")
    st.subheader("Litigation controls")
    strict_dates_only = st.toggle(
        "STRICT: only expiration or labeled test/report dates",
        value=True
    )
    show_review_needed = st.toggle("Show review-needed table", value=True)

    st.markdown("---")
    st.subheader("Parallel processing")
    workers = st.number_input(
        "Workers",
        min_value=1,
        max_value=max(1, (os.cpu_count() or 2)),
        value=1,
        step=1
    )

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

    settings = ScanSettings(
        max_pages=int(max_pages),
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

    with zipfile.ZipFile(io.BytesIO(zbytes), "r") as z:
        names = [n for n in z.namelist() if n.lower().endswith(SUPPORTED_EXTS) and not n.endswith("/")]
        total = len(names)

        if total == 0:
            st.error("No PDFs found in the ZIP.")
        else:
            pdf_items: List[Tuple[str, bytes]] = [(name, z.read(name)) for name in names]
            completed = 0

            if int(workers) == 1:
                for name, b in pdf_items:
                    status.write(f"Scanning {completed + 1}/{total}: {name}")
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
                        out_rows.append({
                            "record_id": record_id,
                            "created_at_utc": created_at,
                            "filename": name,
                            "sha256": "",
                            "size_bytes": 0,
                            "parsing_method": "error",
                            "ocr_used": False,
                            "max_pages_scanned": settings.max_pages,
                            "flagged": False,
                            "review_needed": True,
                            "reasons": f"ERROR: {e}",
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
                            "evidence": {"error": str(e)},
                            "ruleset_version": RULESET_VERSION,
                            "fed_ruleset_version": FED_RULESET_VERSION,
                            "app_version": APP_VERSION,
                        })
                    completed += 1
                    prog.progress(completed / total)
            else:
                with ProcessPoolExecutor(max_workers=int(workers)) as ex:
                    futures = {ex.submit(scan_one_pdf, name, b, settings): name for name, b in pdf_items}
                    for fut in as_completed(futures):
                        name = futures[fut]
                        record_id = str(uuid.uuid4())
                        created_at = utc_now_iso()
                        status.write(f"Completed {completed + 1}/{total}: {name}")
                        try:
                            row = fut.result()
                            row["record_id"] = record_id
                            row["created_at_utc"] = created_at
                            row["ruleset_version"] = RULESET_VERSION
                            row["fed_ruleset_version"] = FED_RULESET_VERSION
                            row["app_version"] = APP_VERSION
                            out_rows.append(row)
                        except Exception as e:
                            out_rows.append({
                                "record_id": record_id,
                                "created_at_utc": created_at,
                                "filename": name,
                                "sha256": "",
                                "size_bytes": 0,
                                "parsing_method": "error",
                                "ocr_used": False,
                                "max_pages_scanned": settings.max_pages,
                                "flagged": False,
                                "review_needed": True,
                                "reasons": f"ERROR: {e}",
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
                                "evidence": {"error": str(e)},
                                "ruleset_version": RULESET_VERSION,
                                "fed_ruleset_version": FED_RULESET_VERSION,
                                "app_version": APP_VERSION,
                            })
                        completed += 1
                        prog.progress(completed / total)

            # DB writes
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
                    db_insert_event(row["record_id"], "DB_ERROR", {"filename": row["filename"], "error": str(e)})

    st.session_state["batch_rows"] = out_rows

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
        "hemp_reasons": r.get("hemp_reasons", ""),

        "has_delta8": r.get("has_delta8", False),
        "has_delta9": r.get("has_delta9", False),

        "test_date": r.get("test_date", ""),
        "expiration_date": r.get("expiration_date", ""),
        "effective_expiration_date": r.get("effective_expiration_date", ""),
        "expired_before_cutoff": r.get("expired_before_cutoff", False),
        "expired_as_of_scan": r.get("expired_as_of_scan", False),
        "has_early_date": r.get("has_early_date", False),

        "pot_total_thc_pct": (r.get("potency") or {}).get("total_thc_pct"),
        "pot_delta9_pct": (r.get("potency") or {}).get("delta9_pct"),
        "pot_thca_pct": (r.get("potency") or {}).get("thca_pct"),
        "pot_delta8_pct": (r.get("potency") or {}).get("delta8_pct"),
        "pot_total_potential_thc_pct": (r.get("potency") or {}).get("total_potential_thc_pct"),

        "reasons": r.get("reasons", ""),

        "sha256": r.get("sha256", ""),
        "parsing_method": r.get("parsing_method", ""),
        "ocr_used": r.get("ocr_used", False),
        "pages_scanned": r.get("max_pages_scanned", 0),

        "percent_map_count": r.get("percent_map_count", 0),
        "percent_map_source": r.get("percent_map_source", ""),

        "ruleset_version": r.get("ruleset_version", ""),
        "fed_ruleset_version": r.get("fed_ruleset_version", ""),
        "app_version": r.get("app_version", ""),
    } for r in rows])

    total = len(df)
    client_flag_ct = int(df["flagged"].sum())
    review_ct = int(df["review_needed"].sum())
    hemp_flag_ct = int(df["hemp_flagged"].sum())
    err_ct = int((df["parsing_method"] == "error").sum())
    ocr_ct = int(df["ocr_used"].sum())

    c1, c2, c3, c4, c5, c6 = st.columns([1, 1, 1, 1, 1, 1])
    c1.metric("Total scanned", total)
    c2.metric("Client flagged", client_flag_ct)
    c3.metric("Review-needed", review_ct)
    c4.metric("Hemp-flagged", hemp_flag_ct)
    c5.metric("OCR used", ocr_ct)
    c6.metric("Errors", err_ct)

    st.divider()
    st.subheader("Batch results")
    st.dataframe(df, use_container_width=True)

    if show_review_needed:
        st.subheader("Review-needed")
        review_df = df[df["review_needed"] == True].copy()
        if len(review_df) == 0:
            st.info("No review-needed rows.")
        else:
            st.dataframe(review_df, use_container_width=True)

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
