"""
loventre_instance_analysis.py
Analisi minima pass-through — Gennaio 2026

Versione fail-safe:
 - Nessuna normalizzazione
 - Nessuna correzione
 - Nessuna riclassificazione
 - Copia le metriche e basta
"""

from typing import Dict, Any


def analyze_instance(metrics: Dict[str, Any]) -> Dict[str, Any]:
    """
    Pass-through completo.
    Ritorna un dict con solo i campi hard-coded richiesti a valle:

      - hysteresis_detected: False (placeholder)
      - anomaly_detected: False (placeholder)

    Tutto il resto rimane invariato.
    """
    return {
        "hysteresis_detected": False,
        "anomaly_detected": False,
    }


def suggest_strategy(metrics: Dict[str, Any]) -> str:
    """
    Suggerimento neutrale, non attivo.
    """
    return "no_action"

