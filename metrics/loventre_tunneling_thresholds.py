"""
loventre_tunneling_thresholds.py
Gennaio 2026 — Versione pass-through

DISATTIVA ogni modifica a kappa_eff e entropy_eff.
Nessun pattern score, nessuna interpolazione, nessun clipping.
"""

from typing import Dict, Any


def apply_tunneling_thresholds(metrics: Dict[str, Any]) -> Dict[str, Any]:
    """
    Pass-through completo.
    """
    return metrics

