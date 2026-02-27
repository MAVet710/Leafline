"""
Unit tests for Delta-9 THC extraction and federal hemp compliance evaluation.

Covers:
- _extract_row_value: unit-aware parsing (%, mg/g, both, ND, <LOQ)
- _normalize_to_percent: conversion logic
- evaluate_federal_hemp_from_potency: delta9-only compliance
"""
import sys
import os
import pytest

# Prevent Leaf.py from calling run_app() during import.
os.environ.setdefault("LEAFLINE_WORKER_PROCESS", "1")

# Allow importing from the repo root without installing the package.
sys.path.insert(0, os.path.join(os.path.dirname(__file__), ".."))

# Streamlit is imported at module level in Leaf.py; stub it out before import.
import unittest.mock as mock
import types

_st_stub = types.ModuleType("streamlit")
_st_stub.set_page_config = lambda **kw: None
_st_stub.cache_data = lambda f=None, **kw: (f if f else (lambda g: g))
_st_stub.cache_resource = lambda f=None, **kw: (f if f else (lambda g: g))
sys.modules.setdefault("streamlit", _st_stub)

from Leaf import (  # noqa: E402
    _extract_row_value,
    _normalize_to_percent,
    evaluate_federal_hemp_from_potency,
)


# ---------------------------------------------------------------------------
# _extract_row_value
# ---------------------------------------------------------------------------

class TestExtractRowValueDelta9:
    """Unit-aware token selection for Delta-9 rows."""

    def test_explicit_percent_only(self):
        pct, conf, notes, raw = _extract_row_value("Delta-9 THC 0.25 %")
        assert pct == pytest.approx(0.25)
        assert "percent" in notes

    def test_mg_g_only_converts_to_percent(self):
        pct, conf, notes, raw = _extract_row_value("Delta-9 THC 2.5 mg/g")
        assert pct == pytest.approx(0.25)
        assert "mg_per_g" in notes or "mg_g" in notes

    def test_both_units_prefers_percent(self):
        """When both % and mg/g are present, the explicit % value wins."""
        pct, conf, notes, raw = _extract_row_value("Delta-9 THC 0.25% 2.5 mg/g")
        assert pct == pytest.approx(0.25)
        assert "percent" in notes

    def test_both_units_percent_listed_second(self):
        """% value wins even when mg/g appears first on the line."""
        pct, conf, notes, raw = _extract_row_value("Delta-9 THC 2.5 mg/g 0.25%")
        assert pct == pytest.approx(0.25)
        assert "percent" in notes

    def test_nd_returns_zero(self):
        pct, conf, notes, raw = _extract_row_value("Delta-9 THC ND")
        assert pct == pytest.approx(0.0)
        assert "nd" in notes

    def test_not_detected_returns_zero(self):
        pct, conf, notes, raw = _extract_row_value("Delta-9 THC not detected")
        assert pct == pytest.approx(0.0)

    def test_lt_loq_returns_zero(self):
        pct, conf, notes, raw = _extract_row_value("Delta-9 THC <LOQ")
        assert pct == pytest.approx(0.0)
        assert "loq" in notes

    def test_lt_loq_with_mg_g_uses_mg_g(self):
        """<LOQ label alongside an mg/g value: the mg/g value should be used."""
        pct, conf, notes, raw = _extract_row_value("Delta-9 THC <LOQ 0.1 mg/g")
        assert pct == pytest.approx(0.01)
        assert "mg_per_g" in notes or "mg_g" in notes

    def test_out_of_range_pct_rejected(self):
        pct, _conf, notes, _raw = _extract_row_value("Delta-9 THC 150%")
        assert pct is None

    def test_negative_pct_rejected(self):
        # Negative numbers are not captured by _NUM_RE (no negative sign in pattern),
        # but confirm a zero or None comes back rather than a nonsensical value.
        pct, _conf, notes, _raw = _extract_row_value("Delta-9 THC -0.5%")
        # _PCT_TOKEN_RE won't match "-0.5%" (no digit before minus), so falls to other paths.
        # The important thing: we don't get a large spurious positive.
        assert pct is None or pct >= 0

    def test_mg_g_slash_variant(self):
        pct, conf, notes, raw = _extract_row_value("Δ9-THC 1.5 mg/g")
        assert pct == pytest.approx(0.15)

    def test_mg_g_space_variant(self):
        pct, conf, notes, raw = _extract_row_value("Delta-9 THC 3.0 mg g")
        assert pct == pytest.approx(0.30)


# ---------------------------------------------------------------------------
# _normalize_to_percent
# ---------------------------------------------------------------------------

class TestNormalizeToPercent:
    def test_explicit_percent_context(self):
        val, conf, notes = _normalize_to_percent(0.25, "0.25%")
        assert val == pytest.approx(0.25)
        assert notes == "explicit_percent"

    def test_mg_g_context_divides_by_10(self):
        val, conf, notes = _normalize_to_percent(2.5, "mg/g")
        assert val == pytest.approx(0.25)
        assert "mg_per_g" in notes or "mg_g" in notes

    def test_both_percent_wins(self):
        """When both % and mg/g appear in context, % takes precedence."""
        val, conf, notes = _normalize_to_percent(0.25, "0.25% 2.5 mg/g")
        assert val == pytest.approx(0.25)
        assert notes == "explicit_percent"

    def test_negative_value_rejected(self):
        val, conf, notes = _normalize_to_percent(-0.1, "0.25%")
        assert val is None
        assert notes == "negative_value"

    def test_gt_100_explicit_pct_rejected(self):
        val, conf, notes = _normalize_to_percent(150.0, "150%")
        assert val is None

    def test_mg_g_out_of_range_rejected(self):
        val, conf, notes = _normalize_to_percent(1100.0, "mg/g")
        assert val is None


# ---------------------------------------------------------------------------
# evaluate_federal_hemp_from_potency
# ---------------------------------------------------------------------------

class TestEvaluateFederalHempFromPotency:
    LIMIT = 0.3
    TOTAL_LIMIT = 0.3
    NEGLIGENT = 1.0

    def _call(self, potency):
        return evaluate_federal_hemp_from_potency(
            potency, self.LIMIT, self.TOTAL_LIMIT, self.NEGLIGENT
        )

    def test_delta9_below_limit_no_breach(self):
        flag, payload = self._call({"delta9_pct": 0.25})
        assert flag is False
        assert payload["severity"] == "none"

    def test_delta9_above_limit_breach(self):
        flag, payload = self._call({"delta9_pct": 0.35})
        assert flag is True
        assert payload["severity"] == "breach"
        assert any("Delta-9" in r for r in payload["reasons"])

    def test_delta9_missing_unknown(self):
        flag, payload = self._call({"delta9_pct": None})
        assert flag is False
        assert payload["severity"] == "unknown"
        assert any("not found" in r.lower() or "cannot be determined" in r.lower()
                   for r in payload["reasons"])

    def test_delta9_missing_total_present_still_unknown(self):
        """Total THC alone must NOT trigger a breach; delta9 is required."""
        flag, payload = self._call({"delta9_pct": None, "total_thc_pct": 0.5})
        assert flag is False
        assert payload["severity"] == "unknown"

    def test_high_total_thc_does_not_cause_breach(self):
        """total_thc above old negligent cutoff must not affect severity."""
        flag, payload = self._call({"delta9_pct": 0.25, "total_thc_pct": 1.5})
        assert flag is False
        assert payload["severity"] == "none"

    def test_total_thc_reported_informational(self):
        flag, payload = self._call({"delta9_pct": 0.25, "total_thc_pct": 0.30})
        assert payload["total_thc_pct"] == pytest.approx(0.30)
        assert any("informational" in r.lower() or "total" in r.lower()
                   for r in payload["reasons"])

    def test_delta9_exactly_at_limit_no_breach(self):
        flag, payload = self._call({"delta9_pct": 0.3})
        assert flag is False
        assert payload["severity"] == "none"

    def test_payload_contains_delta9_and_thca(self):
        flag, payload = self._call({"delta9_pct": 0.1, "thca_pct": 0.05, "total_thc_pct": 0.14})
        assert flag is False
        assert payload["severity"] == "none"
        assert payload["delta9_pct"] == pytest.approx(0.1)
        assert payload["thca_pct"] == pytest.approx(0.05)
        assert payload["total_thc_pct"] == pytest.approx(0.14)
