# /app.py
import io
import os
import re
import json
import uuid
import zipfile
import hashlib
import sqlite3
from dataclasses import dataclass, asdict
from datetime import datetime, date, timezone
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


# ============================
# App constants
# ============================
APP_NAME = "Leafline"
APP_VERSION = "2.8.0"
DB_PATH = "leafline_audit.db"
SUPPORTED_EXTS = (".pdf",)

# ============================
# Client-required flag logic
# ============================
EXPIRY_CUTOFF = date(2021, 11, 24)
EARLY_YEAR_CUTOFF = 2020
CLIENT_THC_THRESHOLD = 0.3  # percent

DELTA8_TERMS = [
    r"delta\s*[-]?\s*8", r"\bdelta8\b", r"Δ\s*8", r"\bΔ8\b", r"\bD8\b", r"\bd8[-\s]*thc\b"
]
DELTA9_TERMS = [
    r"delta\s*[-]?\s*9", r"\bdelta9\b", r"Δ\s*9", r"\bΔ9\b", r"\bD9\b", r"\bd9[-\s]*thc\b"
]

THC_CONTEXT_TERMS = [r"\bTHC\b", r"tetrahydrocannabinol", r"\bcannabinoid\b", r"\bpotency\b"]

RULESET_VERSION = "client_flag_v6_litigation_evidence_parallel"
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
    return "" if v is None else f"{v:.3f}%"


# ============================
# Evidence structures
# ============================
@dataclass(frozen=True)
class PotencyEvidence:
    key: str
    value_pct: float
    source: str  # "table" | "ocr_row" | "inline_text"
    page: Optional[int] = None
    raw_name: Optional[str] = None
    raw_value: Optional[str] = None
    snippet: Optional[str] = None


@dataclass(frozen=True)
class DateEvidence:
    kind: str  # "expiration" | "labeled_report_date" | "fallback_any_date"
    value: str  # ISO date
    source: str  # "regex"
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
        flagged, reasons,
        expiration_date, earliest_date_found, expired_before_cutoff, has_early_date,
        hemp_flag, hemp_severity, hemp_reasons, hemp_delta9_pct, hemp_thca_pct, hemp_total_thc_pct,
        potency_json, evidence_json, percent_map_count
    ) VALUES (?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?, ?)
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
# Dates (litigation-friendly)
# ============================
MONTH_NAME_RE = r"(?:jan(?:uary)?|feb(?:ruary)?|mar(?:ch)?|apr(?:il)?|may|jun(?:e)?|jul(?:y)?|aug(?:ust)?|sep(?:t(?:ember)?)?|oct(?:ober)?|nov(?:ember)?|dec(?:ember)?)"


def _extract_date_tokens(text: str) -> List[str]:
    if not text:
        return []
    candidates: List[str] = []
    candidates += re.findall(r"\b\d{1,2}[/-]\d{1,2}[/-]\d{2,4}\b", text)
    candidates += re.findall(r"\b\d{4}-\d{2}-\d{2}\b", text)
    candidates += re.findall(rf"\b{MONTH_NAME_RE}\s+\d{{1,2}}(?:,)?\s+\d{{4}}\b", text, flags=re.IGNORECASE)
    candidates += re.findall(rf"\b\d{{1,2}}\s+{MONTH_NAME_RE}(?:,)?\s+\d{{4}}\b", text, flags=re.IGNORECASE)
    return list(dict.fromkeys(candidates))


def extract_expiration_date(text: str) -> Tuple[Optional[date], Optional[DateEvidence]]:
    if not text:
        return None, None
    patterns = [
        rf"(expiration\s*date|exp\s*date|expires?|expir\w*)\s*[:\-]?\s*(\d{{1,2}}[/-]\d{{1,2}}[/-]\d{{2,4}})",
        rf"(expiration\s*date|exp\s*date|expires?|expir\w*)\s*[:\-]?\s*(\d{{4}}-\d{{2}}-\d{{2}})",
        rf"(expiration\s*date|exp\s*date|expires?|expir\w*)\s*[:\-]?\s*({MONTH_NAME_RE}\s+\d{{1,2}}(?:,)?\s+\d{{4}})",
        rf"(expiration\s*date|exp\s*date|expires?|expir\w*)\s*[:\-]?\s*(\d{{1,2}}\s+{MONTH_NAME_RE}(?:,)?\s+\d{{4}})",
    ]
    for pat in patterns:
        m = re.search(pat, text, flags=re.IGNORECASE)
        if not m:
            continue
        token = m.group(2)
        d = safe_parse_date(token)
        if d:
            snippet = (m.group(0) or "")[:240]
            return d, DateEvidence(kind="expiration", value=d.isoformat(), source="regex", snippet=snippet)
    return None, None


def extract_labeled_report_dates(text: str) -> List[Tuple[date, DateEvidence]]:
    if not text:
        return []

    label_re = (
        r"(date\s*of\s*analysis|analysis\s*date|report\s*date|date\s*reported|"
        r"test\s*date|tested\s*on|date\s*tested|received\s*date|date\s*received|"
        r"sample\s*date|collection\s*date|collected\s*on|date\s*collected|issued\s*on)"
    )
    date_token_re = (
        rf"(\d{{1,2}}[/-]\d{{1,2}}[/-]\d{{2,4}}|\d{{4}}-\d{{2}}-\d{{2}}|"
        rf"{MONTH_NAME_RE}\s+\d{{1,2}}(?:,)?\s+\d{{4}}|\d{{1,2}}\s+{MONTH_NAME_RE}(?:,)?\s+\d{{4}})"
    )

    out: List[Tuple[date, DateEvidence]] = []
    for m in re.finditer(rf"{label_re}\s*[:\-]?\s*{date_token_re}", text, flags=re.IGNORECASE):
        token = m.group(2)
        d = safe_parse_date(token)
        if not d:
            continue
        snippet = (m.group(0) or "")[:240]
        out.append((d, DateEvidence(kind="labeled_report_date", value=d.isoformat(), source="regex", snippet=snippet)))

    uniq: Dict[str, Tuple[date, DateEvidence]] = {}
    for d, ev in out:
        uniq[d.isoformat()] = (d, ev)
    return sorted(list(uniq.values()), key=lambda x: x[0])


def extract_fallback_any_dates(text: str, limit: int = 25) -> List[Tuple[date, DateEvidence]]:
    tokens = _extract_date_tokens(text)
    out: List[Tuple[date, DateEvidence]] = []
    for tok in tokens[:limit]:
        d = safe_parse_date(tok)
        if not d:
            continue
        out.append((d, DateEvidence(kind="fallback_any_date", value=d.isoformat(), source="regex", snippet=tok[:120])))
    uniq: Dict[str, Tuple[date, DateEvidence]] = {}
    for d, ev in out:
        uniq[d.isoformat()] = (d, ev)
    return sorted(list(uniq.values()), key=lambda x: x[0])


# ============================
# Potency extraction with provenance
# ============================
def extract_percent_column_maps_from_tables(pdf_bytes: bytes, max_pages: int = 6) -> Dict[str, Dict[str, Any]]:
    """
    Returns { analyte_key: {pct: float, loq: float|None, raw_name: str, source: str, page: int, raw_pct: str} }
    """
    results: Dict[str, Dict[str, Any]] = {}
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

                loq_idx = None
                for i, h in enumerate(header_norm):
                    if "loq" in h:
                        loq_idx = i
                        break

                name_idx = None
                for i, h in enumerate(header_norm):
                    if any(k in h for k in ["analyte", "compound", "cannabinoid", "terpene", "name"]):
                        name_idx = i
                        break
                if name_idx is None:
                    name_idx = 0

                for row in table[1:]:
                    if not row or len(row) <= pct_idx:
                        continue
                    name = (row[name_idx] or "").strip()
                    if not name:
                        continue
                    raw_pct = row[pct_idx]
                    pct_val = _parse_float_or_nd(raw_pct)
                    loq_val = _parse_float_or_nd(row[loq_idx]) if (loq_idx is not None and len(row) > loq_idx) else None
                    if pct_val is None:
                        continue

                    key = _norm(name)
                    existing = results.get(key)
                    if (existing is None) or (pct_val > float(existing.get("pct", -1))):
                        results[key] = {
                            "pct": float(pct_val),
                            "loq": loq_val,
                            "raw_name": name,
                            "raw_pct": str(raw_pct)[:80],
                            "source": "table",
                            "page": page_idx,
                        }
    return results


ROW_LINE_RE = re.compile(
    r"""^\s*
        (?P<name>[A-Za-z0-9Δµ\-\(\)\/\.\'\s]{3,}?)
        \s+
        (?P<pct>(?:\d+(?:\.\d+)?|ND))
        (?:\s+%|\b)
        (?:\s+(?P<mg>(?:\d+(?:\.\d+)?|ND)))?
        (?:\s+(?:LOQ|LLOQ)\s*[:\-]?\s*(?P<loq>\d+(?:\.\d+)?|ND))?
        \s*$
    """,
    re.IGNORECASE | re.VERBOSE
)


def extract_percent_column_maps_from_text(text: str) -> Dict[str, Dict[str, Any]]:
    """
    Returns { analyte_key: {pct: float, loq: float|None, raw_name: str, source: str, snippet: str} }
    """
    results: Dict[str, Dict[str, Any]] = {}
    if not text:
        return results

    lines = [ln.strip() for ln in text.splitlines() if ln.strip()]
    for ln in lines:
        if len(ln) < 6:
            continue
        if re.search(r"prepared for|final authorization|remarks|page \d+ of|\bcoa\b", ln, re.I):
            continue

        m = ROW_LINE_RE.match(ln)
        if not m:
            continue

        name = (m.group("name") or "").strip()
        pct_raw = (m.group("pct") or "").strip()
        loq_raw = (m.group("loq") or "").strip() if m.group("loq") else None

        pct_val = _parse_float_or_nd(pct_raw)
        if pct_val is None:
            continue

        loq_val = _parse_float_or_nd(loq_raw) if loq_raw else None
        key = _norm(name)

        existing = results.get(key)
        if (existing is None) or (pct_val > float(existing.get("pct", -1))):
            results[key] = {
                "pct": float(pct_val),
                "loq": loq_val,
                "raw_name": name,
                "raw_pct": pct_raw[:40],
                "source": "ocr_row",
                "page": None,
                "snippet": ln[:240],
            }

    return results


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


def extract_inline_potency_from_text(text: str) -> List[PotencyEvidence]:
    if not text or "%" not in text:
        return []

    evidences: List[PotencyEvidence] = []

    for key, pats in INLINE_POTENCY_PATTERNS.items():
        best: Optional[Tuple[float, str, str]] = None  # (val, raw, snippet)
        for pat in pats:
            for m in re.finditer(pat, text, flags=re.IGNORECASE | re.DOTALL):
                raw = (m.group(1) or "").strip()
                val = _parse_float_or_nd(raw)
                if val is None:
                    continue
                snippet = (m.group(0) or "")[:240]
                if best is None or val > best[0]:
                    best = (float(val), raw, snippet)

        if best is not None:
            evidences.append(PotencyEvidence(
                key=key,
                value_pct=best[0],
                source="inline_text",
                page=None,
                raw_name=key,
                raw_value=best[1],
                snippet=best[2],
            ))

    return evidences


def _lookup_pct_from_map(percent_map: Dict[str, Dict[str, Any]], patterns: List[str]) -> Optional[Dict[str, Any]]:
    for k, v in percent_map.items():
        for pat in patterns:
            if re.search(pat, k, flags=re.IGNORECASE):
                return v
    return None


def extract_potency_with_evidence(percent_map: Dict[str, Dict[str, Any]], text: str) -> Tuple[Dict[str, Optional[float]], List[PotencyEvidence]]:
    ev: List[PotencyEvidence] = []

    def add_from_map(out_key: str, patterns: List[str]):
        hit = _lookup_pct_from_map(percent_map, patterns)
        if not hit:
            return None
        val = float(hit["pct"])
        ev.append(PotencyEvidence(
            key=out_key,
            value_pct=val,
            source=str(hit.get("source") or "table"),
            page=hit.get("page"),
            raw_name=str(hit.get("raw_name") or ""),
            raw_value=str(hit.get("raw_pct") or ""),
            snippet=str(hit.get("snippet") or "")[:240] if hit.get("snippet") else None,
        ))
        return val

    delta8 = add_from_map("delta8_pct", [r"delta\s*[-]?\s*8", r"\bΔ8\b", r"\bd8\b", r"delta\s*8\s*thc", r"d8[-\s]*thc"])
    delta9 = add_from_map("delta9_pct", [r"delta\s*[-]?\s*9", r"\bΔ9\b", r"\bd9\b", r"delta\s*9\s*thc", r"d9[-\s]*thc"])
    thca = add_from_map("thca_pct", [r"\bthca\b", r"thc[-\s]*a", r"tetrahydrocannabinolic"])
    total_thc = add_from_map("total_thc_pct", [r"total\s*thc\b"])
    total_potential_thc = add_from_map("total_potential_thc_pct", [r"total\s*potential\s*thc\b"])

    computed_total: Optional[float] = None
    if total_thc is None and (delta9 is not None or thca is not None):
        d9 = float(delta9 or 0.0)
        a = float(thca or 0.0)
        computed_total = d9 + (a * THCA_DECARB_FACTOR)

    final_total = total_thc
    if final_total is None and computed_total is not None:
        final_total = computed_total
    if final_total is None and total_potential_thc is not None:
        final_total = total_potential_thc

    potency = {
        "delta8_pct": delta8,
        "delta9_pct": delta9,
        "thca_pct": thca,
        "total_thc_pct": final_total,
        "total_potential_thc_pct": total_potential_thc,
    }

    # Fill missing from inline text (but never overwrite stronger sources)
    inline_evs = extract_inline_potency_from_text(text)
    for iev in inline_evs:
        if potency.get(iev.key) is None:
            potency[iev.key] = float(iev.value_pct)
            ev.append(iev)

    return potency, ev


def thc_over_threshold(potency: Dict[str, Optional[float]], threshold: float) -> Tuple[bool, List[str]]:
    evid: List[str] = []
    for label in ["total_thc_pct", "delta9_pct", "thca_pct", "delta8_pct", "total_potential_thc_pct"]:
        val = potency.get(label)
        if val is None:
            continue
        if float(val) > threshold:
            evid.append(f"{label}={float(val):.3f}%")
            return True, evid
    evid.append("No potency value above threshold")
    return False, evid


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
# Client flag (litigation mode)
# ============================
def evaluate_client_flag_litigation(
    text: str,
    potency: Dict[str, Optional[float]],
    strict_dates_only: bool,
) -> Tuple[bool, Dict[str, Any]]:
    reasons: List[str] = []
    evidence: Dict[str, Any] = {}

    has_delta8 = any_term(text, DELTA8_TERMS) or (potency.get("delta8_pct") is not None)
    has_delta9 = any_term(text, DELTA9_TERMS) or (potency.get("delta9_pct") is not None)
    has_delta = bool(has_delta8 or has_delta9)

    has_thc_context = any_term(text, THC_CONTEXT_TERMS) or any(v is not None for v in potency.values())
    thc_over, thc_ev = thc_over_threshold(potency, CLIENT_THC_THRESHOLD)

    exp_date, exp_ev = extract_expiration_date(text)

    labeled_dates = extract_labeled_report_dates(text)
    fallback_dates = extract_fallback_any_dates(text) if not strict_dates_only else []
    date_pool = labeled_dates if labeled_dates else fallback_dates

    early_dates = [d for d, _ in date_pool if d.year <= EARLY_YEAR_CUTOFF]
    expired_before_cutoff = bool(exp_date and exp_date < EXPIRY_CUTOFF)
    has_early_date = bool(early_dates)

    if has_delta:
        reasons.append("Delta 8/9 detected")
    else:
        reasons.append("No Delta 8/9 detected")

    if has_thc_context:
        reasons.append("THC context detected")
    else:
        reasons.append("No THC context detected")

    if thc_over:
        reasons.append(f"THC above {CLIENT_THC_THRESHOLD}% detected")
    else:
        reasons.append(f"No THC above {CLIENT_THC_THRESHOLD}% detected")

    if exp_date:
        reasons.append(f"Expiration date found: {exp_date.isoformat()}")
    else:
        reasons.append("No expiration date found")

    if expired_before_cutoff:
        reasons.append(f"Expired before {EXPIRY_CUTOFF.isoformat()}")

    if labeled_dates:
        reasons.append("Used labeled report/test dates")
    else:
        reasons.append("No labeled report/test dates found" + ("" if strict_dates_only else " (used fallback date scan)"))

    if has_early_date:
        reasons.append(f"Contains relevant date in {EARLY_YEAR_CUTOFF} or earlier (e.g., {early_dates[0].isoformat()})")

    date_condition = expired_before_cutoff or has_early_date

    # Litigation-grade gating: if strict and no labeled dates AND no expiration date, treat as NOT flagged (insufficient evidence)
    if strict_dates_only and (not exp_date) and (not labeled_dates):
        reasons.append("STRICT DATE MODE: insufficient date evidence (no expiration date and no labeled report/test date)")
        date_condition = False

    # Must meet all requirements
    flagged = bool(has_delta and has_thc_context and thc_over and date_condition)

    earliest_found = ""
    if early_dates:
        earliest_found = early_dates[0].isoformat()
    elif date_pool:
        earliest_found = min([d for d, _ in date_pool]).isoformat()

    evidence["thc_over_evidence"] = thc_ev
    evidence["expiration_evidence"] = asdict(exp_ev) if exp_ev else None
    evidence["date_evidence_pool"] = [asdict(ev) for _, ev in date_pool[:10]]

    details = {
        "has_delta8": has_delta8,
        "has_delta9": has_delta9,
        "expiration_date": exp_date.isoformat() if exp_date else "",
        "earliest_date_found": earliest_found,
        "expired_before_cutoff": expired_before_cutoff,
        "has_early_date": has_early_date,
        "strict_dates_only": strict_dates_only,
        "used_labeled_dates": bool(labeled_dates),
        "potency": potency,
        "evidence": evidence,
    }
    return flagged, {"reasons": reasons, "details": details}


# ============================
# PDF report export
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
        f"Flag if: (Delta 8 or Delta 9) AND (THC > {CLIENT_THC_THRESHOLD}%) AND "
        f"(Expired before {EXPIRY_CUTOFF.isoformat()} OR labeled report/test date in {EARLY_YEAR_CUTOFF} or earlier).",
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
            f"Extraction: {r.get('parsing_method', '')} (OCR: {bool(r.get('ocr_used'))}, pages: {r.get('max_pages_scanned')})",
            x, y, max_w, size=9, leading=11
        )

        if r.get("expiration_date"):
            y = wrap_text(c, f"Expiration date: {r['expiration_date']}", x, y, max_w, size=9, leading=11)
        if r.get("earliest_date_found"):
            y = wrap_text(c, f"Earliest relevant date found: {r['earliest_date_found']}", x, y, max_w, size=9, leading=11)

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

        ev = r.get("evidence") or {}
        thc_over_ev = ev.get("thc_over_evidence") or []
        if thc_over_ev:
            y = wrap_text(c, "THC evidence:", x, y, max_w, size=9, leading=11)
            for line in thc_over_ev[:6]:
                y = wrap_text(c, f"- {line}", x + 12, y, max_w - 12, size=9, leading=11)

        exp_ev = ev.get("expiration_evidence")
        if exp_ev and exp_ev.get("snippet"):
            y = wrap_text(c, "Expiration snippet:", x, y, max_w, size=9, leading=11)
            y = wrap_text(c, exp_ev["snippet"], x + 12, y, max_w - 12, size=9, leading=11)

        y = wrap_text(c, f"Client reasons: {r.get('reasons', '')}", x, y, max_w, size=9, leading=11)
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


def scan_one_pdf(name: str, pdf_bytes: bytes, settings: ScanSettings) -> Dict[str, Any]:
    """
    Worker-safe: no Streamlit, no DB.
    Returns a full row dict (and event payloads if desired).
    """
    created_at = utc_now_iso()
    sha = sha256_bytes(pdf_bytes)

    text, method, ocr_used = extract_text_hybrid(
        pdf_bytes,
        max_pages=settings.max_pages,
        min_text_len=settings.min_text_len,
        ocr_scale=settings.ocr_scale,
    )

    percent_map = extract_percent_column_maps_from_tables(pdf_bytes, max_pages=settings.max_pages)
    percent_map_source = "tables"
    if len(percent_map) == 0:
        percent_map = extract_percent_column_maps_from_text(text)
        percent_map_source = "ocr_row_parser"

    potency, potency_evidence = extract_potency_with_evidence(percent_map, text)

    flagged, payload = evaluate_client_flag_litigation(
        text=text,
        potency=potency,
        strict_dates_only=settings.strict_dates_only,
    )

    reasons_list = payload["reasons"]
    details = payload["details"]

    hemp_flag = False
    hemp_payload = {"reasons": [], "severity": "none", "delta9_pct": None, "thca_pct": None, "total_thc_pct": None}
    if settings.enable_hemp:
        hemp_flag, hemp_payload = evaluate_federal_hemp_from_potency(
            potency,
            delta9_limit=float(settings.hemp_delta9_limit),
            total_limit=float(settings.hemp_total_limit),
            negligent_cutoff=float(settings.hemp_negligent_cutoff),
        )

    evidence = details.get("evidence") or {}
    evidence["potency_evidence"] = [asdict(e) for e in potency_evidence[:25]]

    return {
        "created_at_utc": created_at,
        "filename": name,
        "sha256": sha,
        "size_bytes": len(pdf_bytes),

        "parsing_method": method,
        "ocr_used": ocr_used,
        "max_pages_scanned": settings.max_pages,

        "flagged": bool(flagged),
        "reasons": "; ".join(reasons_list),
        "expiration_date": details.get("expiration_date") or "",
        "earliest_date_found": details.get("earliest_date_found") or "",
        "expired_before_cutoff": details.get("expired_before_cutoff", False),
        "has_early_date": details.get("has_early_date", False),
        "strict_dates_only": details.get("strict_dates_only", True),
        "used_labeled_dates": details.get("used_labeled_dates", False),
        "has_delta8": details.get("has_delta8", False),
        "has_delta9": details.get("has_delta9", False),
        "thc_over_evidence": (evidence.get("thc_over_evidence") or [])[:10],

        "hemp_flag": bool(hemp_flag),
        "hemp_severity": hemp_payload.get("severity", "none"),
        "hemp_reasons": "; ".join(hemp_payload.get("reasons", [])),
        "hemp_delta9_pct": hemp_payload.get("delta9_pct"),
        "hemp_thca_pct": hemp_payload.get("thca_pct"),
        "hemp_total_thc_pct": hemp_payload.get("total_thc_pct"),

        "potency": potency,
        "percent_map_count": len(percent_map),
        "percent_map_source": percent_map_source,

        "evidence": evidence,
    }


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
    st.subheader("Litigation accuracy controls")
    strict_dates_only = st.toggle(
        "STRICT: only use labeled report/test dates (no random date fallback)",
        value=True
    )
    st.caption("Recommended ON for litigation: prevents false flags caused by unrelated dates printed on COAs.")

    st.markdown("---")
    st.subheader("Parallel processing")
    workers = st.number_input("Workers", min_value=1, max_value=max(1, (os.cpu_count() or 2)), value=1, step=1)
    st.caption("Uses separate processes. DB writes remain on main process to avoid locking issues.")

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
    )

    prog = st.progress(0.0)
    status = st.empty()

    with zipfile.ZipFile(io.BytesIO(zbytes), "r") as z:
        names = [n for n in z.namelist() if n.lower().endswith(SUPPORTED_EXTS) and not n.endswith("/")]
        total = len(names)

        if total == 0:
            st.error("No PDFs found in the ZIP.")
        else:
            # Read bytes first (so ZIP handle stays on main thread)
            pdf_items: List[Tuple[str, bytes]] = [(name, z.read(name)) for name in names]

            # Parallel scan (results returned to main process)
            completed = 0
            errors = 0

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
                        errors += 1
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
                            "reasons": f"ERROR: {e}",
                            "expiration_date": "",
                            "earliest_date_found": "",
                            "expired_before_cutoff": False,
                            "has_early_date": False,
                            "strict_dates_only": settings.strict_dates_only,
                            "used_labeled_dates": False,
                            "has_delta8": False,
                            "has_delta9": False,
                            "thc_over_evidence": [],
                            "hemp_flag": False,
                            "hemp_severity": "none",
                            "hemp_reasons": "",
                            "hemp_delta9_pct": None,
                            "hemp_thca_pct": None,
                            "hemp_total_thc_pct": None,
                            "potency": {},
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
                    futures = {
                        ex.submit(scan_one_pdf, name, b, settings): (name, b)
                        for name, b in pdf_items
                    }

                    for fut in as_completed(futures):
                        name, b = futures[fut]
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
                            errors += 1
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
                                "reasons": f"ERROR: {e}",
                                "expiration_date": "",
                                "earliest_date_found": "",
                                "expired_before_cutoff": False,
                                "has_early_date": False,
                                "strict_dates_only": settings.strict_dates_only,
                                "used_labeled_dates": False,
                                "has_delta8": False,
                                "has_delta9": False,
                                "thc_over_evidence": [],
                                "hemp_flag": False,
                                "hemp_severity": "none",
                                "hemp_reasons": "",
                                "hemp_delta9_pct": None,
                                "hemp_thca_pct": None,
                                "hemp_total_thc_pct": None,
                                "potency": {},
                                "percent_map_count": 0,
                                "percent_map_source": "none",
                                "evidence": {"error": str(e)},
                                "ruleset_version": RULESET_VERSION,
                                "fed_ruleset_version": FED_RULESET_VERSION,
                                "app_version": APP_VERSION,
                            })
                        completed += 1
                        prog.progress(completed / total)

            # DB writes on main process only
            for row in out_rows:
                try:
                    db_insert_event(row["record_id"], "INGESTED", {
                        "filename": row["filename"],
                        "sha256": row.get("sha256"),
                        "size_bytes": row.get("size_bytes"),
                        "max_pages_scanned": row.get("max_pages_scanned"),
                        "ocr_used": row.get("ocr_used"),
                        "parsing_method": row.get("parsing_method"),
                        "percent_map_source": row.get("percent_map_source"),
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
                        "reasons": row.get("reasons", ""),
                        "expiration_date": row.get("expiration_date") or None,
                        "earliest_date_found": row.get("earliest_date_found") or None,
                        "expired_before_cutoff": bool(row.get("expired_before_cutoff", False)),
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

                    db_insert_event(row["record_id"], "EVALUATED", {
                        "client_flagged": bool(row.get("flagged", False)),
                        "client_reasons": (row.get("reasons", "").split("; ") if row.get("reasons") else []),
                        "expiration_date": row.get("expiration_date"),
                        "earliest_date_found": row.get("earliest_date_found"),
                        "strict_dates_only": row.get("strict_dates_only"),
                        "used_labeled_dates": row.get("used_labeled_dates"),
                        "thc_over_evidence": row.get("thc_over_evidence", [])[:10],
                        "potency": row.get("potency") or {},
                        "hemp_flag": bool(row.get("hemp_flag", False)),
                        "hemp_severity": row.get("hemp_severity"),
                        "hemp_reasons": (row.get("hemp_reasons", "").split("; ") if row.get("hemp_reasons") else []),
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
        "has_delta8": r.get("has_delta8", False),
        "has_delta9": r.get("has_delta9", False),
        "expired_before_cutoff": r.get("expired_before_cutoff", False),
        "has_early_date": r.get("has_early_date", False),
        "strict_dates_only": r.get("strict_dates_only", True),
        "used_labeled_dates": r.get("used_labeled_dates", False),
        "reasons": r["reasons"],

        "pot_total_thc_pct": (r.get("potency") or {}).get("total_thc_pct"),
        "pot_delta9_pct": (r.get("potency") or {}).get("delta9_pct"),
        "pot_thca_pct": (r.get("potency") or {}).get("thca_pct"),
        "pot_delta8_pct": (r.get("potency") or {}).get("delta8_pct"),
        "pot_total_potential_thc_pct": (r.get("potency") or {}).get("total_potential_thc_pct"),

        "expiration_date": r.get("expiration_date", ""),
        "earliest_date_found": r.get("earliest_date_found", ""),
        "thc_over_evidence": " | ".join(r.get("thc_over_evidence", [])[:2]),

        "sha256": r.get("sha256", ""),
        "parsing_method": r.get("parsing_method", ""),
        "ocr_used": r.get("ocr_used", False),
        "pages_scanned": r.get("max_pages_scanned", 0),

        "percent_map_count": r.get("percent_map_count", 0),
        "percent_map_source": r.get("percent_map_source", ""),

        "hemp_flagged": r.get("hemp_flag", False),
        "hemp_severity": r.get("hemp_severity", ""),
        "hemp_reasons": r.get("hemp_reasons", ""),

        "ruleset_version": r.get("ruleset_version", ""),
        "fed_ruleset_version": r.get("fed_ruleset_version", ""),
        "app_version": r.get("app_version", ""),
    } for r in rows])

    total = len(df)
    client_flag_ct = int(df["flagged"].sum())
    hemp_flag_ct = int(df["hemp_flagged"].sum())
    err_ct = int((df["parsing_method"] == "error").sum())
    ocr_ct = int(df["ocr_used"].sum())

    c1, c2, c3, c4, c5, c6 = st.columns([1, 1, 1, 1, 1, 2])
    c1.metric("Total scanned", total)
    c2.metric("Flagged", client_flag_ct)
    c3.metric("Hemp-flagged", hemp_flag_ct)
    c4.metric("OCR used", ocr_ct)
    c5.metric("Errors", err_ct)
    c6.metric("% rows parsed", int(df["percent_map_count"].fillna(0).sum()))

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

    # Optional: evidence bundle JSON (litigation friendly)
    evidence_bundle = [{
        "record_id": r["record_id"],
        "filename": r["filename"],
        "sha256": r.get("sha256"),
        "flagged": r.get("flagged"),
        "reasons": r.get("reasons"),
        "potency": r.get("potency"),
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
