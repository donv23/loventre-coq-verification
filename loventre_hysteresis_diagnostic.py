"""
loventre_hysteresis_diagnostic.py

Modulo diagnostico per la rilevazione di isteresi informazionale
nel Loventre Engine.

ATTENZIONE:
- NON modifica la decisione globale
- NON modifica la risk_class
- NON altera il CANON
- Aggiunge SOLO informazione esplicativa

Uso tipico:
    from loventre_hysteresis_diagnostic import detect_hysteresis
"""

from __future__ import annotations

from typing import Dict, Any


def detect_hysteresis(metrics: Dict[str, Any]) -> Dict[str, Any]:
    """
    Rileva isteresi informazionale come:
    - superamento passato di una soglia critica
    - stato attuale apparentemente sotto soglia
    - ma collasso decisionale irreversibile

    La funzione:
    - legge SOLO campi esistenti
    - scrive SOLO 'hysteresis_detected'
    """

    hysteresis = False

    entropy = metrics.get("entropy_eff")
    kappa = metrics.get("kappa_eff")
    horizon = metrics.get("horizon_flag")

    lg = metrics.get("loventre_global", {}) or {}
    decision = lg.get("global_decision")

    # Condizione minimale e robusta:
    # - decisione BLACKHOLE
    # - ma parametri non estremi
    if decision == "BLACKHOLE":
        if entropy is not None and kappa is not None:
            if entropy < 0.9 and kappa > -1.0:
                hysteresis = True

    metrics["hysteresis_detected"] = hysteresis
    return metrics

