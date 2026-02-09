"""
V21 NEXT — TREND CLASSIFIER
Legge la memoria V21 per identificare traiettorie.
"""

from .l21_memory_core import tail_memory

def classify_trend(window=20):
    """
    Esamina le ultime N osservazioni e determina:
    - stable     → prevalgono SAFE
    - explore    → prevalgono SAFE_ACCESSIBLE
    - collapse   → prevalgono BLACKHOLE
    - unknown    → nessun dato utile
    """
    recent = tail_memory(window)
    if not recent:
        return "unknown"

    safe = 0
    acc = 0
    bh = 0

    for r in recent:
        dec = r.get("decision")
        if dec == "SAFE":
            safe += 1
        elif dec in ("SAFE_ACCESSIBLE", "P_ACC", "ACCESSIBLE"):
            acc += 1
        elif r.get("is_blackhole"):
            bh += 1

    total = safe + acc + bh
    if total == 0:
        return "unknown"

    if bh > safe + acc:
        return "collapse"
    if acc > safe:
        return "explore"
    return "stable"

