"""
loventre_tsp_family_scaling_NOISY.py

TSP Family Scaling con rumore distruttivo sulle coordinate.
STEP A – Entropia ↑
"""

# ---------------------------------------------------------
# BOOTSTRAP PATH
# ---------------------------------------------------------

import os
import sys
PROJECT_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if PROJECT_ROOT not in sys.path:
    sys.path.insert(0, PROJECT_ROOT)

# ---------------------------------------------------------
# IMPORT
# ---------------------------------------------------------

import math
import random
from typing import List, Tuple, Dict, Any

from metrics.loventre_tunneling import compute_potential, p_tunnel, expected_attempts
from experiments.loventre_tsp_toy import (
    explore_tsp_instance,
    aggregate_tsp_geometry,
    ALPHA_TSP,
    BETA_TSP,
    A_MIN_TSP,
)

# ---------------------------------------------------------
# TSP NOISY GENERATOR
# ---------------------------------------------------------

def generate_noisy_coords(
    n_cities: int,
    radius: float = 1.0,
    noise_sigma: float = 0.8,
    seed: int = 0,
) -> List[Tuple[float, float]]:
    """
    Città su circonferenza + rumore gaussiano forte.
    """
    rnd = random.Random(seed + 999 * n_cities)
    coords: List[Tuple[float, float]] = []

    for i in range(n_cities):
        angle = 2.0 * math.pi * i / n_cities
        x = radius * math.cos(angle)
        y = radius * math.sin(angle)

        x += rnd.gauss(0.0, noise_sigma)
        y += rnd.gauss(0.0, noise_sigma)

        coords.append((x, y))

    return coords


def max_states_for_n(n: int) -> int:
    if n <= 6:
        return 10_000
    if n <= 10:
        return 30_000
    if n <= 15:
        return 50_000
    return 80_000


# ---------------------------------------------------------
# ANALISI
# ---------------------------------------------------------

def analyze_tsp_n(n: int, energy: float, n_budget: int) -> Dict[str, Any]:
    coords = generate_noisy_coords(n, radius=1.0, noise_sigma=0.8, seed=42)
    max_states = max_states_for_n(n)

    metrics_list, best_len, _ = explore_tsp_instance(coords, max_states=max_states)
    kappa_eff, entropy_eff = aggregate_tsp_geometry(metrics_list)

    V0 = compute_potential(kappa_eff, entropy_eff, alpha=ALPHA_TSP, beta=BETA_TSP)
    p = p_tunnel(V0, A_MIN_TSP, energy)
    EN = expected_attempts(p)

    P_succ = 1.0 - (1.0 - p) ** n_budget if p > 0 else 0.0

    return {
        "n": n,
        "kappa_eff": kappa_eff,
        "entropy_eff": entropy_eff,
        "V0": V0,
        "p": p,
        "EN": EN,
        "P_success": P_succ,
    }


# ---------------------------------------------------------
# MAIN
# ---------------------------------------------------------

def main() -> None:
    energy = 0.5
    n_budget = 1000
    n_list = [5, 8, 10, 12, 15, 18, 20]

    print("==============================================================")
    print("=== TSP NOISY – STEP A (Entropia ↑) ===========================")
    print("==============================================================")
    print(f"E = {energy}, N_budget = {n_budget}")
    print()

    print("n   kappa_eff  entropy_eff   V0      p_tunnel   E[N]     P_success")
    print("------------------------------------------------------------------")

    for n in n_list:
        r = analyze_tsp_n(n, energy, n_budget)
        print(
            f"{r['n']:2d}  "
            f"{r['kappa_eff']:9.3f} "
            f"{r['entropy_eff']:11.3f} "
            f"{r['V0']:7.3f} "
            f"{r['p']:9.3e} "
            f"{r['EN']:8.2e} "
            f"{r['P_success']:9.3e}"
        )


if __name__ == "__main__":
    main()

