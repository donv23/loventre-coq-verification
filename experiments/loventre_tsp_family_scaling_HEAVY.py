"""
loventre_tsp_family_scaling_HEAVY.py

Esperimento di scala per una famiglia di problemi TSP_n.
"""

# ---------------------------------------------------------
# BOOTSTRAP PATH CANONICO (necessario per esecuzione standalone)
# ---------------------------------------------------------

import os
import sys

PROJECT_ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), ".."))
if PROJECT_ROOT not in sys.path:
    sys.path.insert(0, PROJECT_ROOT)

# ---------------------------------------------------------
# IMPORT STANDARD
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
# 1. Utility comuni
# ---------------------------------------------------------

def success_probability(p: float, n_trials: int) -> float:
    if n_trials <= 0 or p <= 0.0:
        return 0.0
    if p >= 1.0:
        return 1.0

    log_fail_one = math.log1p(-p)
    log_fail_all = n_trials * log_fail_one
    if log_fail_all < -700.0:
        return 1.0
    return max(0.0, min(1.0, 1.0 - math.exp(log_fail_all)))


def decision_from_probability(p_success: float) -> str:
    if p_success >= 0.9:
        return "Altamente raccomandato"
    if p_success >= 0.5:
        return "Raccomandato"
    if p_success >= 0.1:
        return "Marginale"
    if p_success >= 0.01:
        return "Molto rischioso"
    return "Quasi impossibile"


# ---------------------------------------------------------
# 2. Generatore di istanze TSP_n
# ---------------------------------------------------------

def generate_tsp_coords_family(
    n_cities: int, radius: float = 1.0, seed: int = 0
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


def max_states_for_n(n_cities: int) -> int:
    if n_cities <= 6:
        return 10_000
    if n_cities <= 10:
        return 30_000
    if n_cities <= 15:
        return 50_000
    if n_cities <= 20:
        return 80_000
    return 100_000


# ---------------------------------------------------------
# 3. Analisi singola istanza
# ---------------------------------------------------------

def analyze_tsp_n(n_cities: int, energy: float, n_budget: int) -> Dict[str, Any]:
    coords = generate_tsp_coords_family(n_cities, radius=1.0, seed=42)
    max_states = max_states_for_n(n_cities)

    metrics_list, best_length, best_path = explore_tsp_instance(
        coords, max_states=max_states
    )

    kappa_eff, entropy_eff = aggregate_tsp_geometry(metrics_list)
    V0 = compute_potential(kappa_eff, entropy_eff, alpha=ALPHA_TSP, beta=BETA_TSP)
    p = p_tunnel(V0, A_MIN_TSP, energy)
    EN = expected_attempts(p)
    P_succ = success_probability(p, n_budget)

    return {
        "n_cities": n_cities,
        "kappa_eff": kappa_eff,
        "entropy_eff": entropy_eff,
        "V0": V0,
        "p_tunnel": p,
        "EN": EN,
        "P_success": P_succ,
        "decision": decision_from_probability(P_succ),
        "best_length": best_length,
        "best_path": best_path,
        "max_states": max_states,
    }


# ---------------------------------------------------------
# 4. Esperimento di scala
# ---------------------------------------------------------

def run_family_scaling(energy: float, n_budget: int) -> None:
    n_list = [5, 8, 10, 12, 15, 18, 20, 25, 30]

    print("===================================================================")
    print("=== Loventre TSP Family Scaling – HEAVY TEST =======================")
    print("===================================================================")
    print(f"Energia E   : {energy}")
    print(f"N_budget    : {n_budget}")
    print(f"n_list      : {n_list}")
    print()

    header = (
        "n_cities  kappa_eff  entropy_eff   V0       "
        "p_tunnel(E)   E[N]          P_success   decision"
    )
    print(header)
    print("-" * len(header))

    for n in n_list:
        r = analyze_tsp_n(n, energy, n_budget)
        print(
            f"{r['n_cities']:8d}  "
            f"{r['kappa_eff']:9.3f} "
            f"{r['entropy_eff']:11.3f} "
            f"{r['V0']:7.4f}   "
            f"{r['p_tunnel']:11.3e} "
            f"{r['EN']:10.3e} "
            f"{r['P_success']:10.3e} "
            f"{r['decision']}"
        )


# ---------------------------------------------------------
# MAIN
# ---------------------------------------------------------

def _parse_args() -> Tuple[float, int]:
    energy = 0.5
    n_budget = 1000

    if len(sys.argv) >= 2:
        try:
            energy = float(sys.argv[1])
        except ValueError:
            pass

    if len(sys.argv) >= 3:
        try:
            n_budget = int(sys.argv[2])
        except ValueError:
            pass

    return energy, n_budget


def main() -> None:
    energy, n_budget = _parse_args()
    run_family_scaling(energy, n_budget)


if __name__ == "__main__":
    main()

