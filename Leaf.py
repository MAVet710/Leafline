import io
import json
import zipfile
from pathlib import Path

import pandas as pd
import streamlit as st

from scanner import scan_pdf

st.set_page_config(page_title="Leafline COA Scanner", layout="wide")
st.title("Leafline COA Scanner")
debug = st.checkbox("Debug mode", value=False)
compliance_mode = st.selectbox("Compliance mode", ["ma_adult_use", "hemp_cbd"], index=0)
upload = st.file_uploader("Upload ZIP of PDF COAs", type=["zip"])


if upload:
    results = []
    with zipfile.ZipFile(io.BytesIO(upload.getvalue())) as zf:
        names = [n for n in zf.namelist() if n.lower().endswith(".pdf")]
        for idx, name in enumerate(names, start=1):
            pdf_bytes = zf.read(name)
            results.append(scan_pdf(Path(name).name, pdf_bytes, debug=debug, compliance_mode=compliance_mode))
            st.progress(idx / max(len(names), 1), text=f"Processed {idx}/{len(names)}")

    df = pd.DataFrame(results)
    st.dataframe(df, use_container_width=True)
    st.download_button("Download CSV", df.to_csv(index=False).encode("utf-8"), file_name="leafline_results.csv")
    st.download_button("Download JSON evidence bundle", json.dumps(results, indent=2).encode("utf-8"), file_name="leafline_evidence.json")

    if debug:
        st.subheader("Debug Details")
        for r in results:
            with st.expander(r["filename"]):
                st.write("Detected lab:", r.get("detected_lab"))
                st.write("Selected parser profile:", r.get("parser_profile"))
                st.write("Pages scanned:", r.get("page_count"))
                st.write("OCR used:", r.get("debug", {}).get("ocr_used"))
                st.text((r.get("debug", {}).get("raw_text_preview") or "")[:1200])
                st.write("Candidate cannabinoid rows:", r.get("debug", {}).get("candidate_cannabinoid_rows"))
                st.write("Final selected cannabinoid values:", r.get("cannabinoids"))
                st.write("Extracted dates:", r.get("debug", {}).get("extracted_dates"))
                st.write("Field-level confidence:", r.get("field_confidence"))
                st.write("Review needed:", r.get("review_needed"))
                st.write("Flags generated:", r.get("flags"))
