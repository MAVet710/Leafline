import hashlib
from typing import Any, Dict

from extractors import extract_native_text_and_tables, ocr_pages
from parser_profiles.g7_lab_llc import parse_g7
from parser_profiles.mcr_labs import parse_mcr
from parser_profiles.assured_confident_lims import parse_assured
from parser_profiles.smithers_qbench import parse_smithers
from rules import evaluate_compliance


def detect_lab(text: str) -> str:
    if "G7 Lab LLC" in text or "G7LAB.COM" in text:
        return "g7_lab_llc"
    if "MCR Labs" in text or "mcrlabs.com" in text or "MCR-S" in text:
        return "mcr_labs"
    if "Assured Testing Laboratories" in text or "Confident LIMS" in text:
        return "assured_confident_lims"
    if "Smithers AMS LLC" in text or "QBench" in text:
        return "smithers_qbench"
    return "generic"


def _base_result(filename: str, pdf_bytes: bytes, page_count: int, compliance_mode: str) -> Dict[str, Any]:
    return {
        "filename": filename, "sha256": hashlib.sha256(pdf_bytes).hexdigest(), "page_count": page_count,
        "detected_lab": "", "parser_profile": "generic", "client": "", "product_name": "", "strain": "", "sample_id": "",
        "batch_id": "", "client_batch_id": "", "metrc_tag": "", "metrc_source_tag": "", "metrc_sample": "", "metrc_batch": "",
        "sample_type": "", "matrix": "", "specification": "", "date_received": "", "date_tested": "", "date_of_analysis": "",
        "date_reported": "", "report_created": "", "expiration_date": "", "expiration_date_source": "not_found",
        "cannabinoids": {"delta9_thc_pct": None, "delta8_thc_pct": None, "thca_pct": None, "total_thc_pct": None, "total_thc_sum_pct": None, "total_cbd_pct": None, "total_cannabinoids_pct": None, "total_active_cannabinoids_pct": None},
        "terpenes": {"total_terpenes_pct": None},
        "safety_tests": {"pesticides": "", "mycotoxins": "", "microbials": "", "heavy_metals": "", "residual_solvents": "", "vitamin_e_acetate": ""},
        "compliance_mode": compliance_mode, "flags": [], "review_needed": False, "field_confidence": {}, "evidence": {}, "debug": {}
    }


def scan_pdf(filename: str, pdf_bytes: bytes, debug: bool = False, compliance_mode: str = "ma_adult_use") -> Dict[str, Any]:
    parsed = extract_native_text_and_tables(pdf_bytes)
    full_text = "\n".join([p.get("text") or "" for p in parsed["pages"]])
    profile = detect_lab(full_text)
    ocr_used = False
    if not full_text.strip():
        ocr_used = True
        pages = [p["page"] for p in parsed["pages"][:4]]
        ocr = ocr_pages(pdf_bytes, pages)
        for p in parsed["pages"]:
            if p["page"] in ocr:
                p["text"] = ocr[p["page"]]
        full_text = "\n".join([p.get("text") or "" for p in parsed["pages"]])
        profile = detect_lab(full_text)

    result = _base_result(filename, pdf_bytes, parsed["page_count"], compliance_mode)
    if profile == "g7_lab_llc":
        result.update(parse_g7(parsed, filename))
    elif profile == "mcr_labs":
        result.update(parse_mcr(parsed, filename))
    elif profile == "assured_confident_lims":
        result.update(parse_assured(parsed, filename))
    elif profile == "smithers_qbench":
        result.update(parse_smithers(parsed, filename))
    else:
        result["detected_lab"] = "unknown"
        result["parser_profile"] = "generic"
        result["flags"].append("unknown_lab")
        result["review_needed"] = True

    result = evaluate_compliance(result)
    if debug:
        result["debug"] = {
            "detected_lab": result.get("detected_lab"), "selected_parser_profile": result.get("parser_profile"), "pages_scanned": parsed["page_count"],
            "ocr_used": ocr_used, "raw_text_preview": full_text[:3000], "candidate_cannabinoid_rows": {k: v for k, v in result.get("evidence", {}).items() if "thc" in k or "cannabinoid" in k},
            "final_selected_cannabinoid_values": result.get("cannabinoids"), "date_candidates": {k: v for k, v in result.get("evidence", {}).items() if "date" in k or 'report_created' in k},
            "final_selected_dates": {"date_received": result.get("date_received"), "date_tested": result.get("date_tested"), "date_of_analysis": result.get("date_of_analysis"), "date_reported": result.get("date_reported"), "report_created": result.get("report_created"), "expiration_date": result.get("expiration_date")},
            "safety_test_statuses": result.get("safety_tests"), "confidence_by_field": result.get("field_confidence"), "evidence_snippets": result.get("evidence"),
            "flags": result.get("flags"), "review_needed": result.get("review_needed")
        }
    return result
