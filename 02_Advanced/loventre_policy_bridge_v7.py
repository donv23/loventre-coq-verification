"""
LOVENTRE ENGINE v7 — Policy Bridge
Collega LMetricsV7 (Coq) con policy di classificazione Python.
"""

from dataclasses import dataclass
from typing import Dict, Any

# ============================================================
# Dataclass coerente con Coq LMetricsV7
# ============================================================

@dataclass
class LMetricsV7:
    kappa_eff: int
    entropy_eff: int
    mass_eff: int
    inertial_idx: int
    risk_index: int
    meta_label: int

# ============================================================
# Costruttore da JSON
# ============================================================

def lmetrics_v7_from_json(data: Dict[str, Any]) -> LMetricsV7:
    return LMetricsV7(
        kappa_eff      = int(data.get("kappa_eff", 0)),
        entropy_eff    = int(data.get("entropy_eff", 0)),
        mass_eff       = int(data.get("mass_eff", 0)),
        inertial_idx   = int(data.get("inertial_idx", 0)),
        risk_index     = int(data.get("risk_index", 0)),
        meta_label     = int(data.get("meta_label", 0)),
    )

# ============================================================
# Policy Bridge v7
# ============================================================

def policy_bridge_v7(m: LMetricsV7) -> Dict[str, Any]:
    """
    Versione minima:
    meta_label guida la classificazione
    """
    if m.meta_label < 0:
        cls = "invalid"
    elif m.meta_label == 0:
        cls = "baseline"
    elif m.meta_label < 5:
        cls = "weak"
    else:
        cls = "strong"

    return {
        "class_v7": cls,
        "score_v7": m.meta_label,
        "safe_flag": m.meta_label >= 0,
    }

# ============================================================
# API CLI per test
# ============================================================

def classify_json_dict(data: Dict[str, Any]) -> Dict[str, Any]:
    m = lmetrics_v7_from_json(data)
    return policy_bridge_v7(m)

