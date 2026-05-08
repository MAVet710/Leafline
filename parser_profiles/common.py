import re
from datetime import datetime, timedelta
from typing import Dict, List, Optional


def normalize_date(s: str) -> str:
    s = (s or "").strip()
    for fmt in ("%Y-%m-%d", "%m/%d/%Y", "%m-%d-%Y", "%Y/%m/%d"):
        try:
            return datetime.strptime(s, fmt).strftime("%Y-%m-%d")
        except ValueError:
            pass
    return s


def pick_label(lines: List[str], patterns: List[str]):
    for ln in lines:
        txt = ln.strip()
        for pat in patterns:
            m = re.search(pat, txt, flags=re.I)
            if m:
                return m.group(1).strip(), txt
    return "", ""


def parse_pct_from_row(row: str) -> Optional[float]:
    if re.search(r"\b(ND|N/D|Not Detected)\b", row, flags=re.I):
        return 0.0
    if "<loq" in row.lower():
        return None
    m = re.search(r"(\d+(?:\.\d+)?)\s*(?:%|wt\.?%)", row, flags=re.I)
    return float(m.group(1)) if m else None


def derive_expiration(out: Dict, date_fields, source_names):
    for f, src in zip(date_fields, source_names):
        if out.get(f):
            out["expiration_date"] = (datetime.strptime(out[f], "%Y-%m-%d") + timedelta(days=365)).strftime("%Y-%m-%d")
            out["expiration_date_source"] = src
            out["field_confidence"]["expiration_date"] = "medium"
            out["evidence"]["expiration_date"] = f"derived from {f}: {out[f]}"
            return
    out["expiration_date"] = ""
    out["expiration_date_source"] = "not_found"
