from extractors import detect_cannabinoids_from_tables


def test_delta9_percent_from_table_row():
    tables = [[["Analyte", "Result"], ["Delta-9 THC", "0.21 %"]]]
    cands = detect_cannabinoids_from_tables(tables, 1, "native_table")
    d9 = [c for c in cands if c.field == "delta9_pct"][0]
    assert d9.value == 0.21
    assert d9.confidence == "high"
