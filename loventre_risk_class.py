"""
loventre_risk_class.py
RISK Layer — coerente con Coq Loventre_RISK_v11–v13
"""

from loventre_lmetrics_core import LMetrics

# Classe simbolica in stile Coq
P_LIKE = "P_like"
P_ACCESSIBLE = "P_accessible"
NP_BLACK_HOLE = "NP_black_hole"

def classify(m: LMetrics) -> str:
    """
    Restituisce la classe informazionale del seme m,
    riproducendo esattamente il comportamento Coq:
      0      -> P_like
      1      -> P_accessible
      >= 2   -> NP_black_hole
    """
    r = m.risk_level
    if r <= 0:
        return P_LIKE
    if r == 1:
        return P_ACCESSIBLE
    return NP_BLACK_HOLE

