"""
loventre_instance_analysis.py
Analisi dell’istanza Loventre — versione fail-safe
Gennaio 2026
"""

from typing import Dict, Any


# -----------------------------------------------------
# Analisi locale dell’istanza
# -----------------------------------------------------
def analyze_instance(metrics: Dict[str, Any]) -> Dict[str, Any]:
    """
    Analizza una singola istanza di metriche.
    Modalità fail-safe:
      - Nessun parametro è veramente obbligatorio
      - In caso di dati mancanti, restituisce valori neutri
    """

    m = dict(metrics)

    # Recupero sicuro di parametri opzionali
    source = m.get("source", "unknown")
    kappa = float(m.get("kappa_eff", 0.0) or 0.0)
    entropy = float(m.get("entropy_eff", 0.0) or 0.0)
    mass = float(m.get("mass_eff", 1.0) or 1.0)

    # Stima qualitativa semplice
    curvature_ratio = abs(kappa) / (1.0 + mass)
    entropy_weight = abs(entropy) * 0.1

    local_score = curvature_ratio + entropy_weight

    # Annotazioni diagnostiche minime
    return dict(
        local_curvature_ratio=curvature_ratio,
        local_entropy_weight=entropy_weight,
        local_analysis_score=local_score,
        analysis_source=source,
    )


# -----------------------------------------------------
# Strategia suggerita (non vincolante)
# -----------------------------------------------------
def suggest_strategy(metrics: Dict[str, Any]) -> str:
    """
    Suggerisce una strategia descrittiva basata sul punteggio locale.
    Fall-back neutrale per instanze incomplete.
    """

    score = float(metrics.get("local_analysis_score", 0.0) or 0.0)

    if score < 0.2:
        return "NO_ACTION"
    elif score < 1.0:
        return "OBSERVE"
    else:
        return "CONSIDER_RECOVERY"

