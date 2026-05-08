import json
from pathlib import Path
import pytest
from scanner import scan_pdf

BASE = Path(__file__).resolve().parent.parent
EXP = BASE / 'expected_results'
COA = BASE / 'test_coas'


def _ws(s):
    return ' '.join((s or '').split())


def _assert_close(a, b):
    if a is None or b is None:
        assert a == b
    else:
        assert abs(a - b) <= 0.01


@pytest.mark.parametrize('exp_path', sorted(EXP.glob('*.json')))
def test_profiles(exp_path):
    exp = json.loads(exp_path.read_text())
    pdf = COA / exp['filename']
    if not pdf.exists():
        pytest.skip(f'missing fixture {pdf}')
    got = scan_pdf(exp['filename'], pdf.read_bytes(), compliance_mode='ma_adult_use')
    assert got['detected_lab'] == exp['detected_lab']
    assert got['parser_profile'] == exp['parser_profile']
    assert _ws(got.get('product_name')) == _ws(exp.get('product_name'))
    assert got.get('sample_id') == exp.get('sample_id')
    if exp.get('sample_type') is not None:
        assert _ws(got.get('sample_type')) == _ws(exp.get('sample_type'))
    for d in ['date_received','date_tested','date_of_analysis','date_reported','report_created']:
        if exp.get(d):
            assert got.get(d) == exp.get(d)
    for c in ['delta9_thc_pct','delta8_thc_pct','thca_pct','total_thc_pct','total_cannabinoids_pct']:
        if c in exp['cannabinoids']:
            _assert_close(got['cannabinoids'].get(c), exp['cannabinoids'].get(c))
    if exp.get('terpenes', {}).get('total_terpenes_pct') is not None:
        _assert_close(got['terpenes'].get('total_terpenes_pct'), exp['terpenes']['total_terpenes_pct'])
    for k, v in exp.get('safety_tests', {}).items():
        if v:
            assert got['safety_tests'].get(k) == v
    assert got.get('review_needed') == exp.get('review_needed')
