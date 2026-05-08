import json
from pathlib import Path

import pytest

from scanner import scan_pdf
from rules import evaluate_compliance


BASE = Path(__file__).resolve().parent.parent
COA_DIR = BASE / "test_coas"
EXP_DIR = BASE / "expected_results"


def _norm_space(s: str) -> str:
    return " ".join((s or "").split())


@pytest.mark.parametrize("expected_file", sorted(EXP_DIR.glob("FL-*.json")))
def test_g7_expected_values(expected_file: Path):
    expected = json.loads(expected_file.read_text())
    pdf_path = COA_DIR / expected["filename"]
    if not pdf_path.exists():
        pytest.skip(f"Missing fixture PDF: {pdf_path}")

    result = scan_pdf(pdf_path.name, pdf_path.read_bytes(), compliance_mode="ma_adult_use")

    assert result["detected_lab"] == expected["detected_lab"]
    assert _norm_space(result["product_name"]) == _norm_space(expected["product_name"])
    assert result["sample_type"] == expected["sample_type"]
    assert result["specification"] == expected["specification"]
    assert result["date_of_analysis"] == expected["date_of_analysis"]
    assert result["expiration_date"] == expected["expiration_date"]
    assert abs(result["cannabinoids"]["delta9_thc_pct"] - expected["cannabinoids"]["delta9_thc_pct"]) <= 0.01
    assert abs(result["cannabinoids"]["thca_pct"] - expected["cannabinoids"]["thca_pct"]) <= 0.01
    assert abs(result["cannabinoids"]["total_thc_pct"] - expected["cannabinoids"]["total_thc_pct"]) <= 0.01
    assert result["review_needed"] == expected["review_needed"]


def test_compliance_mode_behavior():
    base = {"flags": [], "cannabinoids": {"delta9_thc_pct": 1.0}}
    ma = evaluate_compliance({**base, "compliance_mode": "ma_adult_use"})
    hemp = evaluate_compliance({**base, "compliance_mode": "hemp_cbd"})
    assert "delta9_above_0.3" not in ma["flags"]
    assert "delta9_above_0.3" in hemp["flags"]
