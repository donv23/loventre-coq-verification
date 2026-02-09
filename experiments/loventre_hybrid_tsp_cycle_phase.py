"""
C5.D — HYBRID PHASE TRANSITION (TSP ⊕ Cycle barrier)

Transizione continua P-like → NP-like ottenuta
mischiando una barriera ciclica globale sopra TSP,
a energia e budget fissi.
"""

# ============================================================
# BOOTSTRAP PATH (REGOLA AUREA)
# ============================================================

import os
import sys

ROOT_DIR = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if ROOT_DIR not in sys.path:
    sys.path.insert(0, ROOT_DIR)

# ============================================================
# IMPORT
# ============================================================

import math
import random
from typing import List, Tuple

from loventre_tsp_toy import (
    explore_tsp_instance,
    aggregate_tsp_geometry,
    ALPHA_TSP,
    BETA_TSP,
    A_MIN_TSP,
)

from metrics.loventre_tunneling import (
    compute_potential,
    p_tunnel,
    expected_attempts,
)

# ============================================================
# Generatore TSP AUTOCONTENUTO
# ============================================================

def generate_tsp_coords_family(
    n_cities: int, radius: float = 1.0, seed: int = 42
) -> List[Tuple[float, float]]:
    rnd = random.Random(seed + 1000 * n_cities)
    coords: List[Tuple[float, float]] = []

    for i in range(n_cities):
        angle = 2.0 * math.pi * i / n_cities
        r = radius * (0.7 + 0.3 * rnd.random())
        x = r * math.cos(angle) + 0.1 * (rnd.random() - 0.5)
        y = r * math.sin(angle) + 0.1 * (rnd.random() - 0.5)
        coords.append((x, y))

    return coords

# ============================================================
# Utility
# ============================================================

def success_probability(p: float, n_trials: int) -> float:
    if n_trials <= 0:
        return 0.0
    if p <= 0.0:
        return 0.0
    if p >= 1.0:
        return 1.0
    log_fail = n_trials * math.log1p(-p)
    if log_fail < -700.0:
        return 1.0
    return max(0.0, min(1.0, 1.0 - math.exp(log_fail)))

# ============================================================
# C5.D — HYBRID PHASE
# ============================================================

def run_hybrid_phase(
    n_cities: int = 14, energy: float = 0.5, n_budget: int = 1000
) -> None:
    print("====================================================================")
    print("=== HYBRID TSP ⊕ CYCLE — PHASE TRANSITION (C5.D) ====================")
    print("====================================================================")
    print(f"n = {n_cities}, E = {energy}, N_budget = {n_budget}")
    print()

    coords = generate_tsp_coords_family(n_cities)
    metrics_list, _, _ = explore_tsp_instance(coords, max_states=80000)
    kappa_tsp, entropy_tsp = aggregate_tsp_geometry(metrics_list)

    # incremento di barriera ciclica (calibrato su C5 precedenti)
    DELTA_V_CYCLE = 0.35

    print("lambda  kappa_eff  entropy_eff   V0        p_tunnel     E[N]      P_success")
    print("----------------------------------------------------------------------------")

    for lam in [i / 10.0 for i in range(0, 11)]:
        V0 = (
            compute_potential(
                kappa_tsp,
                entropy_tsp,
                alpha=ALPHA_TSP,
                beta=BETA_TSP,
            )
            + lam * DELTA_V_CYCLE
        )

        p = p_tunnel(V0, A_MIN_TSP, energy)
        EN = expected_attempts(p)
        P_succ = success_probability(p, n_budget)

        print(
            f"{lam:5.2f}   "
            f"{kappa_tsp:9.3f} "
            f"{entropy_tsp:11.3f} "
            f"{V0:7.4f}   "
            f"{p:11.3e} "
            f"{EN:10.3e} "
            f"{P_succ:10.3e}"
        )

    print()
    print("Nota:")
    print(" - Energia e budget fissi.")
    print(" - La transizione dipende SOLO dalla struttura globale (lambda).")
    print(" - Questo è il test chiave C5.D.")


if __name__ == "__main__":
    run_hybrid_phase()

