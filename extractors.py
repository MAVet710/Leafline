import io
import re
from dataclasses import dataclass
from typing import Any, Dict, List, Optional, Tuple

import pdfplumber
from PIL import Image
import pypdfium2 as pdfium
import pytesseract


CONF_ORDER = {"none": 0, "low": 1, "medium": 2, "high": 3}


@dataclass
class Candidate:
    field: str
    value: Any
    confidence: str
    method: str
    snippet: str = ""
    page: Optional[int] = None
    reason: str = ""


def extract_native_text_and_tables(pdf_bytes: bytes) -> Dict[str, Any]:
    pages = []
    with pdfplumber.open(io.BytesIO(pdf_bytes)) as pdf:
        for i, page in enumerate(pdf.pages, start=1):
            text = page.extract_text() or ""
            tables = page.extract_tables() or []
            pages.append({"page": i, "text": text, "tables": tables})
    return {"pages": pages, "page_count": len(pages)}


def ocr_pages(pdf_bytes: bytes, page_numbers: List[int]) -> Dict[int, str]:
    doc = pdfium.PdfDocument(pdf_bytes)
    out: Dict[int, str] = {}
    for p in page_numbers:
        bitmap = doc[p - 1].render(scale=2)
        pil = bitmap.to_pil()
        if not isinstance(pil, Image.Image):
            continue
        out[p] = pytesseract.image_to_string(pil) or ""
    return out


def _find_first(patterns: List[str], text: str) -> Optional[str]:
    for pat in patterns:
        m = re.search(pat, text, flags=re.IGNORECASE)
        if m:
            return m.group(1).strip()
    return None


def detect_metadata(text: str, page: int, method: str) -> List[Candidate]:
    cands: List[Candidate] = []
    lab = _find_first([r"lab(?:oratory)?\s*[:\-]\s*([^\n]+)", r"tested\s+by\s*[:\-]\s*([^\n]+)"], text)
    if lab:
        cands.append(Candidate("lab_name", lab, "high", method, page=page, reason="header label"))
    product = _find_first([r"product\s*name\s*[:\-]\s*([^\n]+)", r"sample\s*name\s*[:\-]\s*([^\n]+)"], text)
    if product:
        cands.append(Candidate("product_name", product, "high", method, page=page, reason="header label"))
    batch = _find_first([r"batch\s*(?:id|#|number)?\s*[:\-]\s*([^\n]+)", r"lot\s*(?:id|#)?\s*[:\-]\s*([^\n]+)"], text)
    if batch:
        cands.append(Candidate("batch_id", batch, "medium", method, page=page, reason="id label"))
    sample = _find_first([r"sample\s*(?:id|#|number)?\s*[:\-]\s*([^\n]+)"], text)
    if sample:
        cands.append(Candidate("sample_id", sample, "medium", method, page=page, reason="id label"))
    return cands


def detect_dates(text: str, page: int, method: str) -> List[Candidate]:
    mapping = {
        "analysis_completed_date": [r"analysis\s*completed\s*[:\-]\s*([0-9/\-\.]+)", r"completed\s*[:\-]\s*([0-9/\-\.]+)"],
        "report_date": [r"report\s*date\s*[:\-]\s*([0-9/\-\.]+)", r"date\s*issued\s*[:\-]\s*([0-9/\-\.]+)"],
        "test_date": [r"test\s*date\s*[:\-]\s*([0-9/\-\.]+)"],
        "expiration_date": [r"exp(?:iration|iry)?\s*date\s*[:\-]\s*([0-9/\-\.]+)"]
    }
    out = []
    for field, pats in mapping.items():
        val = _find_first(pats, text)
        if val:
            out.append(Candidate(field, val, "high", method, page=page, reason="date label"))
    return out


def detect_cannabinoids_from_tables(tables: List[List[List[str]]], page: int, method: str) -> List[Candidate]:
    out = []
    aliases = {
        "delta9_pct": ["delta-9", "delta 9", "d9 thc", "Δ9", "delta9 thc"],
        "delta8_pct": ["delta-8", "delta 8", "d8 thc", "Δ8", "delta8 thc"],
        "thca_pct": ["thca"],
        "total_thc_pct": ["total thc"],
        "total_potential_thc_pct": ["total potential thc", "total cannabinoids"]
    }
    for table in tables:
        for row in table:
            row_s = " | ".join([(c or "") for c in row])
            lower = row_s.lower()
            for field, names in aliases.items():
                if any(n in lower for n in names):
                    m = re.search(r"(\d+(?:\.\d+)?)\s*%", row_s)
                    if not m:
                        m = re.search(r"(\d+(?:\.\d+)?)\s*mg\s*/?\s*g", row_s, flags=re.I)
                        if m:
                            val = float(m.group(1)) / 10.0
                            out.append(Candidate(field, val, "medium", method, snippet=row_s, page=page, reason="table row mg/g converted"))
                    else:
                        out.append(Candidate(field, float(m.group(1)), "high", method, snippet=row_s, page=page, reason="table row percent"))
    return out
