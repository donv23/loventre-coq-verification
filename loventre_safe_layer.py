"""
loventre_safe_layer.py
SAFE Layer — identico al SAFE Coq v11–v13
"""

from loventre_lmetrics_core import LMetrics, mkMetrics

def enforce_safe(m: LMetrics) -> LMetrics:
    """
    Abbassa risk_level di 1 ma non sotto 0
    Coq:
      0 -> m
      S n -> mkMetrics n
    """
    r = m.risk_level
    if r <= 0:
        return m
    return mkMetrics(r - 1)

