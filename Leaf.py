import io
import re
import hashlib
from dataclasses import dataclass
from datetime import datetime, date
from typing import Dict, List, Tuple, Optional

import streamlit as st
import pdfplumber
import fitz  # PyMuPDF
from PIL import Image
import pytesseract
from dateutil import parser as dateparser

from reportlab.lib.pagesizes import letter
from reportlab.lib.units import inch
from reportlab.pdfgen import canvas


# ----------------------------
# CONFIG / RULE PACKS (STARTER)
# ----------------------------

STATE_OPTIONS = ["MA", "NY", "NJ"]
PRODUCT_TYPES = ["Flower", "Pre-roll", "Concentrate", "Vape", "Edible", "Topical", "Tincture"]

# Starter: required panels by state + product type.
# NOTE: This is a "starter pack" structure. You should replace/expand with the client’s vetted requirements.
REQUIRED_PANELS: Dict[str, Dict[str, List[str]]] = {
    "MA": {
        "Flower": ["Cannabinoids", "Microbials", "Mycotoxins", "Pesticides", "Heavy Metals", "Moisture", "Water Activity", "Foreign Matter"],
        "Pre-roll": ["Cannabinoids", "Microbials", "Mycotoxins", "Pesticides", "Heavy Metals", "Moisture", "Water Activity", "Foreign Matter"],
        "Concentrate": ["Cannabinoids", "Residual Solvents", "Microbials", "Mycotoxins", "Pesticides", "Heavy Metals"],
        "Vape": ["Cannabinoids", "Residual Solvents", "Heavy Metals", "Microbials"],
        "Edible": ["Cannabinoids", "Microbials", "Mycotoxins", "Heavy Metals", "Pesticides"],
        "Topical": ["Cannabinoids", "Microbials", "Heavy Metals"],
        "Tincture": ["Cannabinoids", "Microbials", "Heavy Metals"],
    },
    "NY": {
        "Flower": ["Cannabinoids", "Terpenes", "Microbials", "Mycotoxins", "Pesticides", "Heavy Metals", "Moisture", "Water Activity", "Foreign Matter"],
        "Pre-roll": ["Cannabinoids", "Terpenes", "Microbials", "Mycotoxins", "Pesticides", "Heavy Metals", "Moisture", "Water Activity", "Foreign Matter"],
        "Concentrate": ["Cannabinoids", "Terpenes", "Residual Solvents", "Microbials", "Mycotoxins", "Pesticides", "Heavy Metals"],
        "Vape": ["Cannabinoids", "Terpenes", "Residual Solvents", "Heavy Metals", "Microbials"],
        "Edible": ["Cannabinoids", "Microbials", "Mycotoxins", "Heavy Metals", "Pesticides"],
        "Topical": ["Cannabinoids", "Microbials", "Heavy Metals"],
        "Tincture": ["Cannabinoids", "Microbials", "Heavy Metals"],
    },
    "NJ": {
        "Flower": ["Cannabinoids", "Microbials", "Mycotoxins", "Pesticides", "Heavy Metals", "Moisture", "Water Activity", "Foreign Matter"],
        "Pre-roll": ["Cannabinoids", "Microbials", "Mycotoxins", "Pesticides", "Heavy Metals", "Moisture", "Water Activity", "Foreign Matter"],
        "Concentrate": ["Cannabinoids", "Residual Solvents", "Microbials", "Mycotoxins", "Pesticides", "Heavy Metals"],
        "Vape": ["Cannabinoids", "Residual Solvents", "Heavy Metals", "Microbials"],
        "Edible": ["Cannabinoids", "Microbials", "Mycotoxins", "Heavy Metals"],
        "Topical": ["Cannabinoids", "Microbials", "Heavy Metals"],
        "Tincture": ["Cannabinoids", "Microbials", "Heavy Metals"],
    },
}

# Keyword patterns used to detect panels in text
PANEL_KEYWORDS = {
    "Cannabinoids": [r"\bcannabinoid", r"\bpotency", r"\bTHC\b", r"\bCBD\b", r"Total\s+THC", r"Total\s+CBD"],
    "Terpenes": [r"\bterpene", r"\bterpenoid", r"\blimonene\b", r"\bmyrcene\b", r"\bcaryophyllene\b"],
    "Moisture": [r"\bmoisture\b"],
    "Water Activity": [r"\bwater\s*activity\b", r"\baw\b"],
    "Microbials": [r"\bmicrobial", r"\bE\.\s*coli\b", r"\bsalmonella\b", r"\byeast\b", r"\bmold\b", r"\bTYMC\b"],
    "Mycotoxins": [r"\bmycotoxin", r"\baflatoxin\b", r"\bochratoxin\b"],
    "Pesticides": [r"\bpesticide", r"\bpyrethrin", r"\bmyclobutanil\b"],
    "Heavy Metals": [r"\bheavy\s*metals?\b", r"\blead\b", r"\barsenic\b", r"\bcadmium\b", r"\bmercury\b"],
    "Residual Solvents": [r"\bsolvent", r"\bresidual\s*solvent", r"\bbutane\b", r"\bpropane\b", r"\bethanol\b"],
    "Foreign Matter": [r"\bforeign\s*matter\b"],
}

# Basic extraction regexes (lab formats vary; this is intentionally flexible)
FIELD_PATTERNS = {
    "lab_name": [r"Lab\s*Name[:\s]+(.+)", r"Certificate\s+of\s+Analysis.*?\n(.+Labs?.*)"],
    "sample_id": [r"Sample\s*ID[:\s]+([A-Za-z0-9\-_]+)", r"Sample\s*:\s*([A-Za-z0-9\-_]+)"],
    "batch_id": [r"Batch\s*(?:#|No\.|Number)?[:\s]+([A-Za-z0-9\-_]+)", r"Lot\s*(?:#|No\.)?[:\s]+([A-Za-z0-9\-_]+)"],
    "matrix": [r"Matrix[:\s]+(.+)", r"Category[:\s]+(.+)", r"Sample\s*Type[:\s]+(.+)"],
    "completed_date": [r"(?:Completed|Reported|Finalized)\s*[:\s]+([0-9]{1,2}[/\-][0-9]{1,2}[/\-][0-9]{2,4})"],
    "received_date": [r"Received\s*[:\s]+([0-9]{1,2}[/\-][0-9]{1,2}[/\-][0-9]{2,4})"],
    "collected_date": [r"Collected\s*[:\s]+([0-9]{1,2}[/\-][0-9]{1,2}[/\-][0-9]{2,4})"],
    "total_thc": [r"Total\s*THC[:\s]+([0-9]+(?:\.[0-9]+)?)\s*%"],
    "total_cbd": [r"Total\s*CBD[:\s]+([0-9]+(?:\.[0-9]+)?)\s*%"],
    "total_cannabinoids": [r"Total\s*Cannabinoids[:\s]+([0-9]+(?:\.[0-9]+)?)\s*%"],
    "moisture": [r"Moisture[:\s]+([0-9]+(?:\.[0-9]+)?)\s*%"],
    "water_activity": [r"Water\s*Activity[:\s]+([0-9]+(?:\.[0-9]+)?)\s*(?:aw)?"],
}


@dataclass
class Finding:
    severity: str  # HOLD, WARN, INFO
    rule_id: str
    title: str
    evidence: str
    recommendation: str


def sha256_bytes(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def safe_parse_date(s: str) -> Optional[date]:
    try:
        d = dateparser.parse(s, dayfirst=False, yearfirst=False)
        if d:
            return d.date()
    except Exception:
        return None
    return None


def extract_text_from_pdf(pdf_bytes: bytes) -> Tuple[str, List[str]]:
    """Return (full_text, per_page_text)."""
    per_page = []
    with pdfplumber.open(io.BytesIO(pdf_bytes)) as pdf:
        for p in pdf.pages:
            txt = p.extract_text() or ""
            per_page.append(txt)
    return "\n\n".join(per_page), per_page


def render_pdf_pages_to_images(pdf_bytes: bytes, zoom: float = 2.0) -> List[Image.Image]:
    """Render PDF pages to PIL images using PyMuPDF (no poppler needed)."""
    images: List[Image.Image] = []
    doc = fitz.open(stream=pdf_bytes, filetype="pdf")
    mat = fitz.Matrix(zoom, zoom)
    for i in range(doc.page_count):
        page = doc.load_page(i)
        pix = page.get_pixmap(matrix=mat, alpha=False)
        img = Image.open(io.BytesIO(pix.tobytes("png")))
        images.append(img)
    return images


def ocr_images(images: List[Image.Image]) -> Tuple[str, List[str], bool]:
    """OCR images; returns (full_text, per_page_text, ocr_ok)."""
    per_page = []
    try:
        for img in images:
            per_page.append(pytesseract.image_to_string(img))
        return "\n\n".join(per_page), per_page, True
    except Exception as e:
        return "", [], False


def extract_fields(text: str) -> Dict[str, str]:
    extracted: Dict[str, str] = {}
    for field, patterns in FIELD_PATTERNS.items():
        for pat in patterns:
            m = re.search(pat, text, flags=re.IGNORECASE | re.MULTILINE)
            if m:
                val = m.group(1).strip()
                # Keep first strong hit
                extracted[field] = val
                break
    return extracted


def detect_panels(text: str) -> Dict[str, bool]:
    detected = {}
    for panel, pats in PANEL_KEYWORDS.items():
        detected[panel] = any(re.search(p, text, flags=re.IGNORECASE) for p in pats)
    return detected


def build_findings(
    state: str,
    product_type: str,
    fields: Dict[str, str],
    panels_detected: Dict[str, bool],
    per_page_text: List[str],
    freshness_days: int,
) -> List[Finding]:
    findings: List[Finding] = []

    required = REQUIRED_PANELS.get(state, {}).get(product_type, [])
    missing = [p for p in required if not panels_detected.get(p, False)]

    # HOLD: missing required panels
    for idx, p in enumerate(missing, start=1):
        findings.append(
            Finding(
                severity="HOLD",
                rule_id=f"{state}-MISS-PANEL-{idx:03d}",
                title=f"Required panel missing: {p}",
                evidence=f"Panel '{p}' was not detected in the document text.",
                recommendation="Request an updated COA showing this panel and its results/methods.",
            )
        )

    # WARN: R&D / non-compliance language
    text_all = "\n".join(per_page_text) if per_page_text else ""
    if re.search(r"\bR&D\b|\bResearch\b|\bfor\s+research\s+only\b|\bQA\b\s*testing", text_all, flags=re.IGNORECASE):
        findings.append(
            Finding(
                severity="WARN",
                rule_id=f"{state}-DOC-TYPE-001",
                title="Document appears to be R&D/QA oriented (not clearly a regulatory compliance COA)",
                evidence="Detected language suggesting R&D/QA/research context in the document.",
                recommendation="Confirm whether a regulatory compliance COA is required for this use case.",
            )
        )

    # WARN: COA freshness
    completed_raw = fields.get("completed_date", "") or fields.get("reported_date", "")
    completed_dt = safe_parse_date(completed_raw) if completed_raw else None
    if completed_raw and completed_dt:
        age = (date.today() - completed_dt).days
        if age > freshness_days:
            findings.append(
                Finding(
                    severity="WARN",
                    rule_id=f"{state}-FRESH-001",
                    title="COA may be outdated per configured freshness threshold",
                    evidence=f"Completed/Reported date: {completed_raw} (approx. {age} days ago). Threshold: {freshness_days} days.",
                    recommendation="Request a more recent COA or document the client’s acceptance of COA age.",
                )
            )
    elif freshness_days > 0:
        findings.append(
            Finding(
                severity="INFO",
                rule_id=f"{state}-FRESH-INFO-001",
                title="COA date not detected for freshness evaluation",
                evidence="Completed/Reported date was not confidently extracted from the document.",
                recommendation="Verify the completion/reported date manually or improve extraction rules for this lab format.",
            )
        )

    # INFO: show potency results if extracted
    if "total_thc" in fields:
        findings.append(
            Finding(
                severity="INFO",
                rule_id=f"{state}-POT-INFO-001",
                title="Total THC extracted",
                evidence=f"Total THC: {fields.get('total_thc')}%",
                recommendation="None.",
            )
        )

    # Derive overall status
    # We don’t add it as finding; we compute it outside.

    return findings


def overall_status(findings: List[Finding]) -> str:
    sev = [f.severity for f in findings]
    if "HOLD" in sev:
        return "HOLD"
    if "WARN" in sev:
        return "NEEDS REVIEW"
    return "PASS"


# ----------------------------
# PDF REPORT GENERATION
# ----------------------------

def wrap_text(c: canvas.Canvas, text: str, x: float, y: float, max_width: float, leading: float = 12) -> float:
    """Draw wrapped text; return new y."""
    words = (text or "").split()
    line = ""
    for w in words:
        test = (line + " " + w).strip()
        if c.stringWidth(test, "Helvetica", 10) <= max_width:
            line = test
        else:
            c.setFont("Helvetica", 10)
            c.drawString(x, y, line)
            y -= leading
            line = w
    if line:
        c.setFont("Helvetica", 10)
        c.drawString(x, y, line)
        y -= leading
    return y


def generate_pdf_report(
    *,
    state: str,
    product_type: str,
    file_name: str,
    file_hash: str,
    fields: Dict[str, str],
    panels_detected: Dict[str, bool],
    findings: List[Finding],
    ruleset_version: str,
    generated_at: str,
) -> bytes:
    buf = io.BytesIO()
    c = canvas.Canvas(buf, pagesize=letter)
    width, height = letter

    margin = 0.75 * inch
    x = margin
    y = height - margin

    # Header
    c.setFont("Helvetica-Bold", 16)
    c.drawString(x, y, "COA Review & Compliance Findings")
    y -= 18

    c.setFont("Helvetica", 10)
    c.drawString(x, y, f"Jurisdiction Applied: {state} | Product Type: {product_type}")
    y -= 14
    c.drawString(x, y, f"Ruleset Version: {ruleset_version}")
    y -= 14
    c.drawString(x, y, f"Generated On: {generated_at}")
    y -= 14
    c.drawString(x, y, f"Source File: {file_name}")
    y -= 14
    c.drawString(x, y, f"SHA-256: {file_hash}")
    y -= 18

    status = overall_status(findings)
    c.setFont("Helvetica-Bold", 14)
    c.drawString(x, y, f"Overall Status: {status}")
    y -= 18

    # Executive Summary
    c.setFont("Helvetica-Bold", 12)
    c.drawString(x, y, "Executive Summary")
    y -= 14

    c.setFont("Helvetica", 10)
    summary_lines = [
        ("Lab", fields.get("lab_name", "Not detected")),
        ("Sample ID", fields.get("sample_id", "Not detected")),
        ("Batch/Lot", fields.get("batch_id", "Not detected")),
        ("Matrix/Category", fields.get("matrix", "Not detected")),
        ("Collected", fields.get("collected_date", "Not detected")),
        ("Received", fields.get("received_date", "Not detected")),
        ("Completed/Reported", fields.get("completed_date", "Not detected")),
        ("Total THC", (fields.get("total_thc") + "%") if fields.get("total_thc") else "Not detected"),
        ("Total CBD", (fields.get("total_cbd") + "%") if fields.get("total_cbd") else "Not detected"),
        ("Total Cannabinoids", (fields.get("total_cannabinoids") + "%") if fields.get("total_cannabinoids") else "Not detected"),
        ("Moisture", (fields.get("moisture") + "%") if fields.get("moisture") else "Not detected"),
        ("Water Activity", fields.get("water_activity", "Not detected")),
    ]
    for k, v in summary_lines:
        c.drawString(x, y, f"{k}: {v}")
        y -= 12
        if y < margin + 120:
            c.showPage()
            y = height - margin

    y -= 8

    # Required vs Detected Panels
    c.setFont("Helvetica-Bold", 12)
    c.drawString(x, y, "Panels (Required vs Detected)")
    y -= 14

    required = REQUIRED_PANELS.get(state, {}).get(product_type, [])
    c.setFont("Helvetica", 10)
    for p in required:
        detected = "Yes" if panels_detected.get(p, False) else "No"
        c.drawString(x, y, f"- {p}: Detected = {detected} | Required = Yes")
        y -= 12
        if y < margin + 120:
            c.showPage()
            y = height - margin

    # Also list additional detected panels not required (optional)
    extras = [p for p, d in panels_detected.items() if d and p not in required]
    if extras:
        y -= 6
        c.setFont("Helvetica-Bold", 11)
        c.drawString(x, y, "Additional Panels Detected (not required by selected ruleset):")
        y -= 14
        c.setFont("Helvetica", 10)
        for p in extras:
            c.drawString(x, y, f"- {p}")
            y -= 12
            if y < margin + 120:
                c.showPage()
                y = height - margin

    # Findings
    c.showPage()
    y = height - margin

    c.setFont("Helvetica-Bold", 14)
    c.drawString(x, y, "Findings")
    y -= 18

    def print_findings(sev: str, y: float) -> float:
        items = [f for f in findings if f.severity == sev]
        if not items:
            return y
        c.setFont("Helvetica-Bold", 12)
        c.drawString(x, y, sev)
        y -= 14
        for fnd in items:
            c.setFont("Helvetica-Bold", 10)
            c.drawString(x, y, f"{fnd.rule_id} — {fnd.title}")
            y -= 12
            c.setFont("Helvetica", 10)
            y = wrap_text(c, f"Evidence: {fnd.evidence}", x + 12, y, max_width=width - 2 * margin - 12)
            y = wrap_text(c, f"Recommended Action: {fnd.recommendation}", x + 12, y, max_width=width - 2 * margin - 12)
            y -= 6
            if y < margin + 60:
                c.showPage()
                y = height - margin
        y -= 8
        return y

    y = print_findings("HOLD", y)
    y = print_findings("WARN", y)
    y = print_findings("INFO", y)

    c.save()
    return buf.getvalue()


# ----------------------------
# STREAMLIT UI
# ----------------------------

st.set_page_config(page_title="COA Scanner (MA / NY / NJ)", layout="wide")

st.title("COA Scanner → PDF Compliance Report (MA / NY / NJ)")
st.caption("Upload a COA (PDF or image), select state + product type, then generate an auditable PDF report.")

colA, colB, colC = st.columns([1, 1, 1])
with colA:
    state = st.selectbox("State / Jurisdiction", STATE_OPTIONS, index=0)
with colB:
    product_type = st.selectbox("Product Type", PRODUCT_TYPES, index=0)
with colC:
    freshness_days = st.number_input("COA freshness threshold (days) — optional", min_value=0, max_value=3650, value=365, step=30)

uploaded = st.file_uploader("Upload COA (PDF, PNG, JPG)", type=["pdf", "png", "jpg", "jpeg"])

if uploaded:
    file_bytes = uploaded.read()
    file_hash = sha256_bytes(file_bytes)
    st.write(f"**File:** {uploaded.name}")
    st.write(f"**SHA-256:** `{file_hash}`")

    is_pdf = uploaded.name.lower().endswith(".pdf")

    extracted_text = ""
    per_page_text: List[str] = []
    used_ocr = False
    ocr_ok = True

    with st.spinner("Extracting text..."):
        if is_pdf:
            # Attempt direct text extraction
            extracted_text, per_page_text = extract_text_from_pdf(file_bytes)

            # If extraction looks empty, OCR fallback
            if len(re.sub(r"\s+", "", extracted_text)) < 500:
                try:
                    images = render_pdf_pages_to_images(file_bytes, zoom=2.0)
                    ocr_text, ocr_pages, ok = ocr_images(images)
                    if ok and len(re.sub(r"\s+", "", ocr_text)) > len(re.sub(r"\s+", "", extracted_text)):
                        extracted_text = ocr_text
                        per_page_text = ocr_pages
                        used_ocr = True
                    else:
                        ocr_ok = ok
                except Exception:
                    ocr_ok = False
        else:
            # Image OCR
            try:
                img = Image.open(io.BytesIO(file_bytes))
                extracted_text = pytesseract.image_to_string(img)
                per_page_text = [extracted_text]
                used_ocr = True
            except Exception:
                ocr_ok = False

    if used_ocr:
        if ocr_ok:
            st.info("OCR was used for extraction (scanned PDF/image detected).")
        else:
            st.warning("OCR could not run (Tesseract missing or OCR error). The report may be incomplete.")

    with st.expander("Show extracted text (debug)"):
        st.text(extracted_text[:20000] if extracted_text else "No text extracted.")

    # Parse fields + panels
    fields = extract_fields(extracted_text)
    panels_detected = detect_panels(extracted_text)

    st.subheader("Detected Summary (preview)")
    pcol1, pcol2 = st.columns(2)
    with pcol1:
        st.write("**Extracted Fields**")
        st.json(fields)
    with pcol2:
        st.write("**Panels Detected**")
        st.json(panels_detected)

    # Build findings
    findings = build_findings(
        state=state,
        product_type=product_type,
        fields=fields,
        panels_detected=panels_detected,
        per_page_text=per_page_text,
        freshness_days=int(freshness_days),
    )

    st.subheader("Findings (preview)")
    st.write(f"**Overall Status:** {overall_status(findings)}")

    def render_finding_card(f: Finding):
        color = {"HOLD": "🟥", "WARN": "🟧", "INFO": "🟦"}.get(f.severity, "⬜")
        st.markdown(f"{color} **{f.severity}** — `{f.rule_id}` — **{f.title}**")
        st.write(f"Evidence: {f.evidence}")
        st.write(f"Recommended Action: {f.recommendation}")
        st.divider()

    for sev in ["HOLD", "WARN", "INFO"]:
        group = [f for f in findings if f.severity == sev]
        if group:
            st.markdown(f"### {sev}")
            for f in group:
                render_finding_card(f)

    # Generate PDF
    ruleset_version = f"{state}_v1.0_{datetime.now().strftime('%Y-%m-%d')}"
    generated_at = datetime.now().strftime("%Y-%m-%d %H:%M:%S")

    pdf_bytes = generate_pdf_report(
        state=state,
        product_type=product_type,
        file_name=uploaded.name,
        file_hash=file_hash,
        fields=fields,
        panels_detected=panels_detected,
        findings=findings,
        ruleset_version=ruleset_version,
        generated_at=generated_at,
    )

    st.download_button(
        label="Download PDF Report",
        data=pdf_bytes,
        file_name=f"COA_Report_{state}_{product_type}_{datetime.now().strftime('%Y%m%d_%H%M%S')}.pdf",
        mime="application/pdf",
    )
else:
    st.info("Upload a COA file to begin.")
