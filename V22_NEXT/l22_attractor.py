"""
V22 — Attractor Detector
Interpreta le transizioni come dinamiche.
"""

from .l22_transition_counter import compute_transition_counts

def classify_attractor(window=100):
    """
    Restituisce uno tra:
    - 'stable_basin'   → SAFE domina la dinamica
    - 'expansion'      → ACCESSIBLE domina
    - 'blackhole_sink' → BH domina
    - 'undefined'      → niente segnale chiaro
    """
    counts = compute_transition_counts(window)
    if not counts:
        return "undefined"

    safe_moves = 0
    acc_moves = 0
    bh_moves  = 0

    for k, v in counts.items():
        if "SAFE" in k:
            safe_moves += v
        if "ACCESS" in k:
            acc_moves += v
        if "BLACKHOLE" in k:
            bh_moves += v

    # domininanza empirica
    if bh_moves > safe_moves + acc_moves:
        return "blackhole_sink"
    if acc_moves > safe_moves:
        return "expansion"
    return "stable_basin"

