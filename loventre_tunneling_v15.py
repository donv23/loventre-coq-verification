"""
loventre_tunneling_v15.py — Prima bozza Tunneling v15
La logica:
 - rischio >= 4  → NP_black_hole stabile
 - rischio 2 o 3 → penombra, 50% di probabilità di scendere a rischio=1
 - rischio < 2   → invariato
"""

from random import random
from loventre_lmetrics_core import mkMetrics
from loventre_risk_class import classify

def tunneling_step(m):
    r = m.risk_level
    c = classify(m)

    # Buco nero "massivo": nessuna fuga
    if r >= 4:
        return mkMetrics(r)  # resta com'è

    # Banda di penombra: chance 50% di rientrare
    if r >= 2:
        if random() < 0.5:
            return mkMetrics(1)
        return mkMetrics(r)

    # Per P e P_accessible nessun cambiamento
    return mkMetrics(r)

if __name__ == "__main__":
    # smoke veloci
    for x in range(0,6):
        import random
        random.seed(0)
        print("risk", x, "→", tunneling_step(mkMetrics(x)))

