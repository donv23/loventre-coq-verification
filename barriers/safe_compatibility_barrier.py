"""
safe_compatibility_barrier.py

Lemma strutturale di compatibilità SAFE.
Verifica che uno stato dichiarato SAFE
non violi invarianti strutturali evidenti.
"""

from typing import Dict, Any


class LoventreSafeCompatibilityError(Exception):
    """Stato SAFE semanticamente incompatibile."""
    pass


def apply_safe_compatibility_barrier(
    metrics: Dict[str, Any],
) -> Dict[str, Any]:
    """
    Se lo stato è dichiarato SAFE, deve rispettare
    condizioni strutturali minime.
    """

    decision = metrics.get("LMetrics_type") or metrics.get("Decision")

    if decision not in {"SAFE", "P_like", "P_STR", "P_ACC"}:
        return metrics

    kappa = float(metrics.get("kappa_eff", 0.0))
    entropy = float(metrics.get("entropy_eff", 0.0))

    # Condizione minimale e dichiarata
    if kappa > 1.0 or entropy > 1.0:
        raise LoventreSafeCompatibilityError(
            "SAFE state incompatible with high curvature or entropy."
        )

    return metrics

