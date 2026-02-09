"""
loventre_hawking_layer.py
Layer pass-through totale — Gennaio 2026

Blocca ogni modifica a kappa_eff, entropy_eff, V0 o altro.
Nessuno smoothing, nessuna curva, nessun clipping.

Serve solo per mantenere compatibilità con pipeline.
"""

from typing import Dict, Any


def apply_hawking_layer(metrics: Dict[str, Any]) -> Dict[str, Any]:
    """
    Pass-through completo.
    """
    return metrics

