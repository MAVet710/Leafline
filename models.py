from dataclasses import dataclass, field, asdict
from typing import Any, Dict, List, Optional


CONF_ORDER = {"none": 0, "low": 1, "medium": 2, "high": 3}


@dataclass
class FieldMatch:
    value: Any = None
    confidence: str = "none"
    evidence: str = ""


@dataclass
class NormalizedResult:
    filename: str
    sha256: str
    page_count: int
    detected_lab: str = ""
    parser_profile: str = "generic"
    product_name: str = ""
    sample_id: str = ""
    batch_id: str = ""
    client_batch_id: str = ""
    client: str = ""
    metrc_tag: str = ""
    sample_type: str = ""
    specification: str = ""
    date_received: str = ""
    date_of_analysis: str = ""
    date_reported: str = ""
    expiration_date: str = ""
    expiration_date_source: str = "not_found"
    cannabinoids: Dict[str, Optional[float]] = field(default_factory=lambda: {
        "delta9_thc_pct": None,
        "delta8_thc_pct": None,
        "thca_pct": None,
        "total_thc_pct": None,
        "total_active_cannabinoids_pct": None,
    })
    compliance_mode: str = "ma_adult_use"
    flags: List[str] = field(default_factory=list)
    review_needed: bool = False
    field_confidence: Dict[str, str] = field(default_factory=dict)
    evidence: Dict[str, str] = field(default_factory=dict)
    debug: Dict[str, Any] = field(default_factory=dict)

    def to_dict(self) -> Dict[str, Any]:
        return asdict(self)
