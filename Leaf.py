import io
import json
import zipfile
from pathlib import Path

import pandas as pd
import streamlit as st

from scanner import scan_pdf

st.set_page_config(page_title="Leafline COA Scanner", layout="wide")
st.title("Leafline COA Scanner (MVP)")
st.caption("Batch PDF COA extraction with confidence scoring and debug evidence.")

debug = st.checkbox("Debug mode", value=False)
upload = st.file_uploader("Upload ZIP of PDF COAs", type=["zip"])


def _to_csv_bytes(df: pd.DataFrame) -> bytes:
    return df.to_csv(index=False).encode("utf-8")


if upload:
    results = []
    with zipfile.ZipFile(io.BytesIO(upload.getvalue())) as zf:
        names = [n for n in zf.namelist() if n.lower().endswith(".pdf")]
        prog = st.progress(0.0)
        for idx, name in enumerate(names, start=1):
            pdf_bytes = zf.read(name)
            results.append(scan_pdf(Path(name).name, pdf_bytes, debug=debug))
            prog.progress(idx / max(len(names), 1), text=f"Processed {idx}/{len(names)}")

    st.success(f"Processed {len(results)} PDFs")
    df = pd.DataFrame(results)
    st.dataframe(df, use_container_width=True)

    st.download_button("Download CSV", _to_csv_bytes(df), file_name="leafline_results.csv", mime="text/csv")

    xlsx_buf = io.BytesIO()
    with pd.ExcelWriter(xlsx_buf, engine="openpyxl") as writer:
        df.drop(columns=["evidence", "debug"], errors="ignore").to_excel(writer, index=False, sheet_name="summary")
    st.download_button("Download XLSX", xlsx_buf.getvalue(), file_name="leafline_results.xlsx")

    json_bundle = json.dumps(results, indent=2, default=str).encode("utf-8")
    st.download_button("Download JSON evidence bundle", json_bundle, file_name="leafline_evidence.json", mime="application/json")

    # simple PDF-like summary fallback as text file with .pdf name is avoided; keep real PDF optional later
    summary = df[["filename", "delta9_pct", "thca_pct", "total_thc_pct", "should_flag", "review_needed"]].to_string(index=False)
    st.download_button("Download Batch Summary (txt)", summary.encode("utf-8"), file_name="leafline_batch_summary.txt")

    if debug:
        st.subheader("Debug Details")
        for r in results:
            with st.expander(r["filename"]):
                st.json(r.get("debug", {}))
