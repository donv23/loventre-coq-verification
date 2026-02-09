"""
monotonicity_barrier.py

Lemma strutturale di monotonicità del rischio.
Teorema-like: verifica, non corregge.
"""

from typing import Dict, Any


class LoventreMonotonicityError(Exception):
    """Violazione della monotonicità del rischio."""
    pass


def _risk_scalar(metrics: Dict[str, Any]) -> float:
    """
    Proiezione minimale del rischio.
    NON è una decisione: è un ordinamento parziale.
    """
    # Scelta minimale e trasparente
    kappa = float(metrics.get("kappa_eff", 0.0))
    entropy = float(metrics.get("entropy_eff", 0.0))
    return max(kappa, entropy)


def apply_monotonicity_barrier(
    metrics_prev: Dict[str, Any],
    metrics_curr: Dict[str, Any],
) -> Dict[str, Any]:
    """
    Se guard invariato e la pressione aumenta,
    il rischio non può diminuire.
    """

    g_prev = metrics_prev.get("loventre_guard")
    g_curr = metrics_curr.get("loventre_guard")

    # Lemma applicabile solo a guard invariato
    if g_prev != g_curr:
        return metrics_curr

    r_prev = _risk_scalar(metrics_prev)
    r_curr = _risk_scalar(metrics_curr)

    if r_curr < r_prev:
        raise LoventreMonotonicityError(
            "Risk decreased under increased pressure (monotonicity violated)."
        )

    return metrics_curr

