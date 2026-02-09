"""
horizon_barrier.py

Lemma strutturale di orizzonte (irreversibilità BH).
Se oltre l'orizzonte, non si può tornare SAFE
a guard canonico invariato.
"""

from typing import Dict, Any


class LoventreHorizonError(Exception):
    """Violazione dell'irreversibilità dell'orizzonte."""
    pass


def _is_black_hole(metrics: Dict[str, Any]) -> bool:
    """
    Predicato minimale di BH.
    Non decide: legge lo stato già assegnato.
    """
    return metrics.get("LMetrics_type") in {
        "NP_like",
        "BH_NP",
        "BLACKHOLE",
    }


def apply_horizon_barrier(
    metrics_prev: Dict[str, Any],
    metrics_curr: Dict[str, Any],
) -> Dict[str, Any]:
    """
    Se il sistema era BH e il guard non cambia,
    non può tornare non-BH.
    """

    g_prev = metrics_prev.get("loventre_guard")
    g_curr = metrics_curr.get("loventre_guard")

    # Lemma valido solo a guard invariato
    if g_prev != g_curr:
        return metrics_curr

    was_bh = _is_black_hole(metrics_prev)
    is_bh = _is_black_hole(metrics_curr)

    if was_bh and not is_bh:
        raise LoventreHorizonError(
            "BH horizon violated: irreversible state became non-BH."
        )

    return metrics_curr

