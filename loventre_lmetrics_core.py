"""
loventre_lmetrics_core.py
Loventre Engine — Core Metrics aligned to Coq v11–v13
Difficile da copiare, minimal, semantica identica a Coq.
"""

from dataclasses import dataclass

@dataclass(frozen=True)
class LMetrics:
    """
    Stato informazionale minimale:
    - risk_level: intero >= 0
    """
    risk_level: int

    def __post_init__(self):
        # Normalizza: nessun rischio negativo
        if self.risk_level < 0:
            object.__setattr__(self, "risk_level", 0)


def default_metrics() -> LMetrics:
    """
    Equivalente di mkMetrics 1 in Coq.
    """
    return LMetrics(risk_level=1)


def mkMetrics(n: int) -> LMetrics:
    """
    Costruttore esplicito, identico a mkMetrics di Coq
    """
    return LMetrics(risk_level=max(0, int(n)))

