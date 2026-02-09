"""
V23 — Cycle Detector
Cerca ricorrenze di attrattori recenti.
"""

from V22_NEXT.l22_attractor import classify_attractor

def detect_cycle(window=100):
    """
    Restituisce uno tra:
    - 'stable_return'  → attrattore attuale uguale al precedente
    - 'switching'      → alternanza fra due stati
    - 'drifting'       → nessuna ripetizione chiara
    - 'unknown'        → nessun segnale
    """
    # valutazione greedy: confrontiamo attrattori vicini
    # chiamando classify_attractor più volte con piccole finestre
    a1 = classify_attractor(window)
    a2 = classify_attractor(window // 2) if window > 2 else a1

    if a1 == "undefined":
        return "unknown"
    if a1 == a2:
        return "stable_return"
    if (a1 != a2) and (a1 not in ("undefined",) and a2 not in ("undefined",)):
        return "switching"
    return "drifting"

