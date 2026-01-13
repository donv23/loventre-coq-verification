#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
LOVENTRE SUGGESTION BRIDGE — v5.3 (stable)
-------------------------------------------
Modulo indipendente che interpreta i risultati
informazionali e produce suggerimenti:
- INSISTI
- VALUTA
- RITIRA
"""

import math

def loventre_suggest_action(metrics: dict):
    """
    Input:
      metrics : dict con campi numerici o None
                expected keys:
                   kappa_eff
                   entropy_eff
                   V0
                   informational_inertia

    Output:
      dict:
       {
         "class": ...   (UNKNOWN/SAFE/ACCESSIBLE/BLACK_HOLE)
         "phase": ...   (UNDEF/EASY/SCHWARZSCHILD/HYPER)
         "gravity": ... (float or None)
         "suggestion": ... (INSISTI/VALUTA/RITIRA/INSUFFICIENT_DATA)
         "explanation": ... (str)
       }
    """

    # Estraggo campi essenziali con fallback None
    kappa = metrics.get("kappa_eff", None)
    entr  = metrics.get("entropy_eff", None)
    V0    = metrics.get("V0", None)
    iner  = metrics.get("informational_inertia", None)

    # 1) Controllo dati insufficienti
    if any(x is None for x in [kappa, entr, V0, iner]):
        return {
            "class": "UNKNOWN",
            "phase": "UNDEF",
            "gravity": None,
            "suggestion": "INSUFFICIENT_DATA",
            "explanation": "Metriche incomplete o mancanti"
        }

    # 2) Fase informazionale (semplificata)
    #    (può essere raffinata in futuro)
    if iner < 0.18:
        phase = "FLAT"
    elif iner < 0.28:
        phase = "EASY"
    else:
        phase = "SCHWARZSCHILD"

    # 3) Gravità informazionale (metrica derivata)
    gravity = abs(kappa - entr)

    # 4) Classificazione
    #    Priorità:
    #    - buchi neri → inerzia alta
    #    - accessibile → inerzia media
    #    - safe → inerzia bassa
    if iner >= 0.33:
        classification = "BLACK_HOLE"
    elif iner >= 0.18:
        classification = "ACCESSIBLE"
    else:
        classification = "SAFE"

    # 5) Suggestione operativa
    if classification == "SAFE":
        sug = "INSISTI"
        expl = "bassa attrazione informazionale"
    elif classification == "ACCESSIBLE":
        sug = "VALUTA"
        expl = "regime accessibile, possibile progresso"
    else:
        sug = "RITIRA"
        expl = "regime attrattivo tipo buco nero"

    return {
        "class": classification,
        "phase": phase,
        "gravity": round(gravity, 3),
        "suggestion": sug,
        "explanation": expl
    }

