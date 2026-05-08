from typing import Any, Dict


def evaluate_compliance(result: Dict[str, Any]) -> Dict[str, Any]:
    flags = list(result.get("flags", []))
    d9 = (result.get("cannabinoids") or {}).get("delta9_thc_pct")
    mode = result.get("compliance_mode", "ma_adult_use")

    if mode == "hemp_cbd" and d9 is not None and d9 > 0.3:
        flags.append("delta9_above_0.3")

    result["flags"] = sorted(set(flags))
    result["should_flag"] = "delta9_above_0.3" in result["flags"]
    return result
