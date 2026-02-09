"""
loventre_meta_decision_engine.py

Motore decisionale globale Loventre (policy-level).
"""

from typing import Any, Dict

# -----------------------------------------------------
# Import corretti (architettura reale)
# -----------------------------------------------------

from metrics.loventre_metrics_bus import ensure_loventre_keys
from dynamics.loventre_instance_analysis import analyze_instance, suggest_strategy


# -----------------------------------------------------
# Motore globale
# -----------------------------------------------------

def meta_decide_instance_with_mass_global(**kwargs: Any) -> Dict[str, Any]:
    """
    Esegue l’analisi globale di un’istanza Loventre e restituisce il metrics bus.
    """

    # Copia difensiva
    metrics = dict(kwargs)

    # Analisi locale dell’istanza
    analysis = analyze_instance(metrics)
    metrics.update(analysis)

    # Suggerimento strategico (non vincolante)
    strategy = suggest_strategy(metrics)
    metrics["strategy_hint"] = strategy

    # Normalizzazione bus Loventre
    metrics = ensure_loventre_keys(metrics)

    return metrics

