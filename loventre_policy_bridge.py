#!/usr/bin/env python3
"""
LOVENTRE POLICY BRIDGE
Classifica LMetrics in:
  * SAFE       (zona P-like)
  * ACCESS     (zona P-accessible / bordo critico)
  * BH         (black-hole zone / NP-like)
"""

def classify_point(metrics: dict) -> str:
    """
    Accetta un dict metriche dal meta-engine:
      {
        "kappa_eff": float,
        "entropy_eff": float,
        "V0": float,
        "p_tunnel": float,
        ...
      }

    Ritorna una stringa: "SAFE", "ACCESS", "BH"
    """

    # Parametri base
    k   = metrics.get("kappa_eff",   0.0)
    ent = metrics.get("entropy_eff", 0.0)
    p   = metrics.get("p_tunnel",    0.0)

    # Condizione di zona nera (black-hole)
    # Alta entropia + alta curvatura + alto tunneling
    if p > 0.70 and ent > 0.60 and k > 0.60:
        return "BH"

    # Zona di accesso borderline (semi-critico)
    if p > 0.25 or ent > 0.35 or k > 0.35:
        return "ACCESS"

    # Tutto sotto soglia => safe
    return "SAFE"

