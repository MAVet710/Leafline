import hashlib
from typing import Any, Dict, List

from extractors import (
    CONF_ORDER,
    Candidate,
    detect_cannabinoids_from_tables,
    detect_dates,
    detect_metadata,
    extract_native_text_and_tables,
    ocr_pages,
)
from rules import evaluate_compliance

FIELDS = [
    "lab_name", "product_name", "batch_id", "sample_id",
    "analysis_completed_date", "expiration_date", "report_date", "test_date",
    "delta9_pct", "delta8_pct", "thca_pct", "total_thc_pct", "total_potential_thc_pct",
    "pass_fail_status",
]


def _pick_best(cands: List[Candidate]) -> Dict[str, Any]:
    chosen: Dict[str, Candidate] = {}
    for c in cands:
        cur = chosen.get(c.field)
        if not cur or CONF_ORDER[c.confidence] > CONF_ORDER[cur.confidence]:
            chosen[c.field] = c
    return chosen


def scan_pdf(filename: str, pdf_bytes: bytes, debug: bool = False) -> Dict[str, Any]:
    parsed = extract_native_text_and_tables(pdf_bytes)
    candidates: List[Candidate] = []
    ocr_used = False
    selected_pages = []

    for p in parsed["pages"]:
        page = p["page"]
        text = p["text"]
        tables = p["tables"]
        selected_pages.append(page)
        candidates.extend(detect_metadata(text, page, "native_text"))
        candidates.extend(detect_dates(text, page, "native_text"))
        candidates.extend(detect_cannabinoids_from_tables(tables, page, "native_table"))

    if len([c for c in candidates if c.field in {"delta9_pct", "thca_pct", "total_thc_pct"}]) == 0:
        ocr_used = True
        ocr = ocr_pages(pdf_bytes, selected_pages[: min(3, len(selected_pages))])
        for pg, text in ocr.items():
            candidates.extend(detect_metadata(text, pg, "ocr_text"))
            candidates.extend(detect_dates(text, pg, "ocr_text"))

    chosen = _pick_best(candidates)
    result: Dict[str, Any] = {
        "filename": filename,
        "sha256": hashlib.sha256(pdf_bytes).hexdigest(),
        "page_count": parsed["page_count"],
        "flags": [],
        "review_needed": True,
        "confidence": {},
        "evidence": {},
    }

    for f in FIELDS:
        c = chosen.get(f)
        if c:
            result[f] = c.value
            result["confidence"][f] = c.confidence
            result["evidence"][f] = {"method": c.method, "page": c.page, "snippet": c.snippet, "reason": c.reason}
        else:
            result[f] = None
            result["confidence"][f] = "none"

    if not result.get("pass_fail_status"):
        full_text = "\n".join([p["text"] for p in parsed["pages"]]).lower()
        if "pass" in full_text:
            result["pass_fail_status"] = "pass"
            result["confidence"]["pass_fail_status"] = "low"
        if "fail" in full_text:
            result["pass_fail_status"] = "fail"
            result["confidence"]["pass_fail_status"] = "low"

    result = evaluate_compliance(result)
    result["extraction_method"] = "native_then_ocr_fallback"
    if debug:
        result["debug"] = {
            "selected_pages": selected_pages,
            "ocr_used": ocr_used,
            "candidate_rows": [c.__dict__ for c in candidates if c.field.endswith("_pct")],
            "final_selected_values": {k: result.get(k) for k in ["delta9_pct", "delta8_pct", "thca_pct", "total_thc_pct", "total_potential_thc_pct"]},
            "confidence_reasons": result["evidence"],
            "flag_reasons": result["flags"],
        }
    return result
