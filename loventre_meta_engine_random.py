"""
LOVENTRE META ENGINE — RANDOMIZED INPUT SOURCE
Versione 2026-01-12
Genera metriche pseudo-casuali coerenti con il motore Loventre e produce
un punto (kappa, entropy, V0, p_tunnel) per testare Policy Bridge.
"""

import random
import math
from datetime import datetime

# Random space configurabile
PARAM_RANGE = [1, 2, 3, 4]
FACTOR_RANGE = [1, 2, 3, 4]

def compute_random_metrics():
    """
    Genera un punto pseudo-random coerente con le idee del motore:
    - kappa_eff cresce quando param e factor sono alti
    - entropy_eff moderata con random jitter
    - V0 aumenta con kappa
    - probabilità di tunneling ~ Gauss tra entropy e V0
    """
    param = random.choice(PARAM_RANGE)
    factor = random.choice(FACTOR_RANGE)

    base = (param + factor) / 10.0
    jitter = random.uniform(-0.05, 0.15)

    kappa_eff = min(max(base + jitter, 0.0), 1.0)
    entropy_eff = min(max(base * 0.75 + random.uniform(-0.05, 0.10), 0.0), 1.0)

    V0 = min(max(kappa_eff * 0.90 + random.uniform(-0.05, 0.10), 0.0), 1.0)

    # effetto valanga rarefatto
    p_tunnel = min(max((entropy_eff + V0) * random.uniform(0.2, 0.8), 0.0), 1.0)

    return {
        "timestamp": datetime.utcnow().isoformat(),
        "param": param,
        "factor": factor,
        "kappa_eff": round(kappa_eff, 4),
        "entropy_eff": round(entropy_eff, 4),
        "V0": round(V0, 4),
        "p_tunnel": round(p_tunnel, 4),
    }

if __name__ == "__main__":
    sample = compute_random_metrics()
    print("🎲 RANDOM SAMPLE:", sample)

