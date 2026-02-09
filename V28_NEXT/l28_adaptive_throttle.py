"""
V28_NEXT/l28_adaptive_throttle.py
Decide come cambiare la velocità del motore in base al rischio istantaneo.
"""

def compute_adaptive_throttle(risk: float) -> str:
    """
    Interpreta risk ∈ [0,1]
    0.00–0.30  → BOOST
    0.30–0.70  → HOLD
    0.70–1.00  → REDUCE
    """
    if risk < 0:
        risk = 0.0
    if risk > 1:
        risk = 1.0

    if risk < 0.30:
        return "BOOST"
    elif risk < 0.70:
        return "HOLD"
    else:
        return "REDUCE"

