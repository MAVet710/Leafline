import re
from typing import Any, Dict
from parser_profiles.common import pick_label, normalize_date, parse_pct_from_row, derive_expiration


def parse_mcr(doc: Dict[str, Any], filename: str) -> Dict[str, Any]:
    lines = []
    for p in doc["pages"]:
        lines.extend((p.get("text") or "").splitlines())
    out = {"detected_lab": "MCR Labs", "parser_profile": "mcr_labs", "field_confidence": {}, "evidence": {}, "flags": [], "review_needed": False}
    labels = {
      "client": [r"^Client\s*[:#-]\s*(.+)$"], "product_name": [r"Sample Name\s*[:#-]\s*(.+)$"],
      "sample_id": [r"Sample ID\s*#?\s*[:#-]\s*(.+)$"], "batch_id": [r"^Batch\s*[:#-]\s*(.+)$"],
      "matrix": [r"^Matrix\s*[:#-]\s*(.+)$"], "metrc_tag": [r"METRC Tag\s*[:#-]\s*(.+)$"],
      "metrc_source_tag": [r"METRC Source Tag\s*[:#-]\s*(.+)$"], "date_received": [r"Date Received\s*[:#-]\s*([0-9/\-]+)"],
      "date_tested": [r"Date\(s\) Tested\s*[:#-]\s*([0-9/\-]+)"], "date_reported": [r"Report Date\s*[:#-]\s*([0-9/\-]+)"]
    }
    for f,pats in labels.items():
      v,e=pick_label(lines,pats); out[f]=normalize_date(v) if f.startswith('date_') else v; out['evidence'][f]=e; out['field_confidence'][f]='high' if v else 'none'

    out["cannabinoids"] = {k: None for k in ["delta9_thc_pct","delta8_thc_pct","thca_pct","total_thc_pct","total_thc_sum_pct","total_cbd_pct","total_cannabinoids_pct","total_active_cannabinoids_pct"]}
    out["terpenes"] = {"total_terpenes_pct": None}
    out["safety_tests"] = {"pesticides": "", "mycotoxins": "", "microbials": "", "heavy_metals": "", "residual_solvents": "", "vitamin_e_acetate": ""}
    mapping={"delta9_thc_pct":["δ9-thc","Δ9-THC","delta 9 thc"],"delta8_thc_pct":["Δ8-THC","delta 8 thc"],"thca_pct":["THCA"],"total_thc_pct":["Total THC = THC + 0.877 * THCA","Total THC"],"total_thc_sum_pct":["Total THC (Sum)"],"total_cbd_pct":["Total CBD"],"total_active_cannabinoids_pct":["Total Active Cannabinoids"]}
    for ln in lines:
      ll=ln.lower()
      for f,keys in mapping.items():
        if any(k.lower() in ll for k in keys):
          v=parse_pct_from_row(ln)
          if v is not None and out['cannabinoids'][f] is None:
            out['cannabinoids'][f]=v; out['field_confidence'][f]='high'; out['evidence'][f]=ln.strip()
      for s in out['safety_tests'].keys():
        if s.replace('_',' ') in ll and 'pass' in ll: out['safety_tests'][s]='Pass'
    derive_expiration(out,["date_of_analysis","date_tested","date_reported"],["derived_from_date_of_analysis","derived_from_date_tested","derived_from_report_date"])
    req=["product_name","sample_id","delta9_thc_pct","thca_pct","total_thc_pct"]
    if any(out['field_confidence'].get(r,'none') in {'none','low'} for r in req): out['review_needed']=True
    return out
