"""
loventre_meta_engine_canon.py
Meta-engine canonico Loventre
FASE 4.5 — Switch controllato v2
Dicembre 2025
"""

from typing import Dict, Any

from loventre_meta_engine import (
    loventre_collect_base_metrics,
    compute_barrier_diagnostic_v4,
)

from loventre_decision_canon import decision_of_metrics
from loventre_decision_canon_v2 import decision_of_metrics_v2


# =========================================================
# Modalità di decisione
# =========================================================

DECISION_MODE = "CANON_V2"
# Possibili valori:
# "ENGINE" | "CANON" | "CANON_V2" | "COMPARE"


# =========================================================
# Invarianti strutturali
# =========================================================

def _assert_metrics(metrics: Any) -> None:
    assert isinstance(metrics, dict), "metrics deve essere dict"


def _assert_decision(decision: Any) -> None:
    if DECISION_MODE == "COMPARE":
        assert isinstance(decision, dict)
        assert "engine" in decision
        assert "canon_v1" in decision
        assert "canon_v2" in decision
    else:
        assert isinstance(decision, str)


# =========================================================
# Meta decisione canonica
# =========================================================

def meta_decide(seed: Dict[str, Any]) -> Dict[str, Any]:
    metrics = loventre_collect_base_metrics(seed)
    _assert_metrics(metrics)

    decision_engine = compute_barrier_diagnostic_v4(metrics)
    decision_canon_v1 = decision_of_metrics(metrics)
    decision_canon_v2 = decision_of_metrics_v2(metrics)

    if DECISION_MODE == "ENGINE":
        decision = decision_engine

    elif DECISION_MODE == "CANON":
        decision = decision_canon_v1

    elif DECISION_MODE == "CANON_V2":
        decision = decision_canon_v2

    elif DECISION_MODE == "COMPARE":
        decision = {
            "engine": decision_engine,
            "canon_v1": decision_canon_v1,
            "canon_v2": decision_canon_v2,
        }

    else:
        raise ValueError("DECISION_MODE non valido")

    _assert_decision(decision)

    return {
        "seed": seed,
        "metrics": metrics,
        "decision": decision,
        "mode": DECISION_MODE
    }

