"""
loventre_classes.py
CLASSES Layer — coerente con Coq Loventre_CLASSES_v11–v13
"""

from loventre_lmetrics_core import LMetrics
from loventre_risk_class import (
    classify,
    P_LIKE,
    P_ACCESSIBLE,
    NP_BLACK_HOLE,
)

def is_P_like(m: LMetrics) -> bool:
    """
    Ritorna True se m soddisfa la classe P_like.
    """
    return classify(m) == P_LIKE

def is_P_accessible(m: LMetrics) -> bool:
    """
    Ritorna True se m soddisfa la classe P_accessible.
    """
    return classify(m) == P_ACCESSIBLE

def is_NP_black_hole(m: LMetrics) -> bool:
    """
    Ritorna True se m è nella classe NP_black_hole.
    """
    return classify(m) == NP_BLACK_HOLE

