from typing import Any, Dict


def evaluate_compliance(result: Dict[str, Any]) -> Dict[str, Any]:
    flags = []
    review_needed = False

    d9 = result.get("delta9_pct")
    conf = result.get("confidence", {}).get("delta9_pct", "none")
    if d9 is None or conf in {"none", "low"}:
        review_needed = True
        flags.append("delta9_not_confident")
    else:
        if d9 > 0.3:
            flags.append("delta9_above_0.3")

    status = result.get("pass_fail_status")
    if status and status.lower() in {"fail", "failed"}:
        flags.append("coa_failed")

    result["flags"] = flags
    result["review_needed"] = review_needed or bool([f for f in flags if "not_confident" in f])
    result["should_flag"] = any(f in {"delta9_above_0.3", "coa_failed"} for f in flags)
    return result
