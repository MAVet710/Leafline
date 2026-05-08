from typing import Any, Dict
from parser_profiles.common import pick_label, normalize_date, parse_pct_from_row, derive_expiration


def parse_g7(doc: Dict[str, Any], filename: str) -> Dict[str, Any]:
    lines=[]
    for p in doc['pages']: lines.extend((p.get('text') or '').splitlines())
    out={"detected_lab":"G7 Lab LLC","parser_profile":"g7_lab_llc","field_confidence":{},"evidence":{},"flags":[],"review_needed":False}
    labels={"product_name":[r"Product\s*[:\-]\s*(.+)$"],"sample_id":[r"Sample ID\s*[:\-]\s*(.+)$"],"batch_id":[r"^Batch ID\s*[:\-]\s*(.+)$"],"client_batch_id":[r"Client Batch ID\s*[:\-]\s*(.+)$"],"client":[r"^Client\s*[:\-]\s*(.+)$"],"metrc_tag":[r"Metrc Tag\s*[:\-]\s*(.+)$"],"sample_type":[r"Sample Type\s*[:\-]\s*(.+)$"],"specification":[r"Specification\s*[:\-]\s*(.+)$"],"date_received":[r"Date Received\s*[:\-]\s*([0-9/\-]+)"],"date_of_analysis":[r"Date of Analysis\s*[:\-]\s*([0-9/\-]+)"],"date_reported":[r"Date Reported\s*[:\-]\s*([0-9/\-]+)"]}
    for f,pats in labels.items():
      v,e=pick_label(lines,pats); out[f]=normalize_date(v) if f.startswith('date_') else v; out['evidence'][f]=e; out['field_confidence'][f]='high' if v else 'none'
    out['cannabinoids']={k:None for k in ["delta9_thc_pct","delta8_thc_pct","thca_pct","total_thc_pct","total_thc_sum_pct","total_cbd_pct","total_cannabinoids_pct","total_active_cannabinoids_pct"]}
    out['terpenes']={"total_terpenes_pct":None}
    out['safety_tests']={"pesticides":"","mycotoxins":"","microbials":"","heavy_metals":"","residual_solvents":"","vitamin_e_acetate":""}
    mapping={"delta9_thc_pct":["Delta 9 THC"],"delta8_thc_pct":["Delta 8 THC"],"thca_pct":["Delta 9 THCA","THCA"],"total_thc_pct":["Total THC=THC+THCAX0.877","Total THC"],"total_cbd_pct":["Total CBD=CBD+CBDAX0.877"],"total_active_cannabinoids_pct":["Total Potency","Total Active Cannabinoids"]}
    for ln in lines:
      for f,keys in mapping.items():
        if any(k.lower() in ln.lower() for k in keys):
          v=parse_pct_from_row(ln)
          if v is not None and out['cannabinoids'][f] is None: out['cannabinoids'][f]=v; out['field_confidence'][f]='high'; out['evidence'][f]=ln.strip()
    derive_expiration(out,["date_of_analysis","date_tested","date_reported"],["derived_from_date_of_analysis","derived_from_date_tested","derived_from_report_date"])
    req=["product_name","sample_type","specification","date_of_analysis","delta9_thc_pct","thca_pct","total_thc_pct"]
    if any(out['field_confidence'].get(r,'none') in {'none','low'} for r in req): out['review_needed']=True
    return out
