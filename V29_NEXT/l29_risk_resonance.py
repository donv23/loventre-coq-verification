"""
V29_NEXT/l29_risk_resonance.py
Analizza la "risonanza" del rischio storico tramite varianza.
"""

def compute_risk_resonance(history):
    """
    history: lista di float ∈ [0,1]
    Ritorna una delle tre classi:
      CALM     → var < 0.02
      PULSED   → var < 0.08
      RESONANT → var >= 0.08
    """
    if not history:
        return "CALM"

    # Clamping
    clamped = [max(0.0, min(1.0, float(x))) for x in history]
    n = len(clamped)
    mean = sum(clamped) / n
    var = sum((x - mean) ** 2 for x in clamped) / n

    if var < 0.02:
        return "CALM"
    elif var < 0.08:
        return "PULSED"
    else:
        return "RESONANT"

