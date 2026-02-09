"""
V27_NEXT/l27_self_tuning.py
Regola di self-tuning: decide se rimanere, adattare o rituned.
"""

def compute_self_tuning(raw: float) -> str:
    """
    0.0–0.33 → RETUNE
    0.33–0.66 → ADAPT
    0.66–1.0 → STEADY
    """
    if raw < 0:
        raw = 0.0
    if raw > 1:
        raw = 1.0

    if raw < 0.33:
        return "RETUNE"
    elif raw < 0.66:
        return "ADAPT"
    else:
        return "STEADY"

