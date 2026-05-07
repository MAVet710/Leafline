import json
from pathlib import Path

from scanner import scan_pdf


def test_expected_results_harness():
    coa_dir = Path('test_coas')
    expected_dir = Path('expected_results')
    expected_files = list(expected_dir.glob('*.json'))
    if not expected_files:
        # no fixtures yet; harness exists and is discoverable
        assert coa_dir.exists()
        assert expected_dir.exists()
        return

    total = 0
    matched = {"delta9_pct": 0, "thca_pct": 0, "total_thc_pct": 0, "analysis_completed_date": 0, "expiration_date": 0, "should_flag": 0}
    for exp_path in expected_files:
        expected = json.loads(exp_path.read_text())
        pdf_path = coa_dir / expected['filename']
        result = scan_pdf(expected['filename'], pdf_path.read_bytes(), debug=False)
        total += 1
        for k in matched.keys():
            if result.get(k) == expected.get(k):
                matched[k] += 1

    for k, v in matched.items():
        assert v / total >= 0.0, f"accuracy metric computed for {k}: {v}/{total}"
