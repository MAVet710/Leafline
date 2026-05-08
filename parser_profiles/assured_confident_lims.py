from typing import Any, Dict
from parser_profiles.common import pick_label, normalize_date, parse_pct_from_row, derive_expiration


def parse_assured(doc: Dict[str, Any], filename: str) -> Dict[str, Any]:
    lines=[]
    for p in doc['pages']: lines.extend((p.get('text') or '').splitlines())
    out={"detected_lab":"Assured Testing Laboratories","parser_profile":"assured_confident_lims","field_confidence":{},"evidence":{},"flags":[],"review_needed":False}
    labels={"client":[r"Client\s*[:\-]\s*(.+)$"],"product_name":[r"Sample\s*[:\-]\s*(.+)$"],"strain":[r"Strain\s*[:\-]\s*(.+)$"],"sample_type":[r"(Plant, Flower - Cured)"],"sample_id":[r"Sample ID\s*[:\-]\s*(.+)$"],"metrc_batch":[r"METRC Batch\s*[:\-]\s*(.+)$"],"metrc_sample":[r"METRC Sample\s*[:\-]\s*(.+)$"],"report_created":[r"Report Created\s*[:\-]\s*([0-9/\-]+)"],"date_received":[r"Date Received\s*[:\-]\s*([0-9/\-]+)"],"date_tested":[r"Date Tested\s*[:\-]\s*([0-9/\-]+)"]}
    for f,pats in labels.items():
      v,e=pick_label(lines,pats); out[f]=normalize_date(v) if 'date' in f or f=='report_created' else v; out['evidence'][f]=e; out['field_confidence'][f]='high' if v else 'none'
    out['cannabinoids']={k:None for k in ["delta9_thc_pct","delta8_thc_pct","thca_pct","total_thc_pct","total_thc_sum_pct","total_cbd_pct","total_cannabinoids_pct","total_active_cannabinoids_pct"]}
    out['terpenes']={"total_terpenes_pct":None}
    out['safety_tests']={"pesticides":"","mycotoxins":"","microbials":"","heavy_metals":"","residual_solvents":"","vitamin_e_acetate":""}
    mapping={"thca_pct":["THCa"],"delta9_thc_pct":["Δ9-THC"],"delta8_thc_pct":["Δ8-THC"],"total_thc_pct":["Total THC"],"total_cbd_pct":["Total CBD"],"total_cannabinoids_pct":["Total Cannabinoids"]}
    for ln in lines:
      for f,keys in mapping.items():
        if any(k.lower() in ln.lower() for k in keys):
          v=parse_pct_from_row(ln)
          if v is not None and out['cannabinoids'][f] is None: out['cannabinoids'][f]=v; out['evidence'][f]=ln.strip(); out['field_confidence'][f]='high'
      if 'total terpenes' in ln.lower():
        v=parse_pct_from_row(ln)
        if v is not None: out['terpenes']['total_terpenes_pct']=v
      for s in out['safety_tests']:
        if s.replace('_',' ') in ln.lower() and 'pass' in ln.lower(): out['safety_tests'][s]='Pass'
    derive_expiration(out,["date_of_analysis","date_tested","date_reported","report_created"],["derived_from_date_of_analysis","derived_from_date_tested","derived_from_report_date","derived_from_report_date"])
    return out
