"""
loventre_tsp_family_scaling_ANTIGREEDY.py

STEP B – TSP anti-greedy:
rompiamo il flusso geodetico randomizzando l'espansione DFS.
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
    compute_distance_stats,
    compute_tsp_state_metrics,
    aggregate_tsp_geometry,
    ALPHA_TSP,
    BETA_TSP,
    A_MIN_TSP,
)

# ---------------------------------------------------------
# TSP GEOMETRICO BASE (senza rumore)
# ---------------------------------------------------------

def generate_geometric_coords(n: int, radius: float = 1.0) -> List[Tuple[float, float]]:
    coords = []
    for i in range(n):
        angle = 2.0 * math.pi * i / n
        coords.append(
            (radius * math.cos(angle), radius * math.sin(angle))
        )
    return coords


# ---------------------------------------------------------
# DFS ANTI-GREEDY (candidati randomizzati)
# ---------------------------------------------------------

def explore_tsp_instance_antigreedy(
    coords: List[Tuple[float, float]],
    max_states: int = 50000,
    seed: int = 0,
) -> Tuple[List[Dict[str, float]], float]:
    rnd = random.Random(seed)
    stats = compute_distance_stats(coords)
    dist = stats["dist"]
    n = stats["n_cities"]

    metrics_list: List[Dict[str, float]] = []
    best_length: float | None = None

    stack: List[Tuple[List[int], int, float]] = [([0], 1 << 0, 0.0)]

    while stack and len(metrics_list) < max_states:
        path, mask, cur_len = stack.pop()
        metrics_list.append(compute_tsp_state_metrics(path, cur_len, stats))

        if len(path) == n:
            tour_len = cur_len + dist[path[-1]][path[0]]
            if best_length is None or tour_len < best_length:
                best_length = tour_len
            continue

        last = path[-1]
        candidates = [
            c for c in range(n) if not (mask & (1 << c))
        ]

        rnd.shuffle(candidates)

        for c in candidates:
            stack.append(
                (
                    path + [c],
                    mask | (1 << c),
                    cur_len + dist[last][c],
                )
            )

    if best_length is None:
        best_length = math.inf

    return metrics_list, best_length


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
    coords = generate_geometric_coords(n)
    max_states = max_states_for_n(n)

    metrics_list, best_len = explore_tsp_instance_antigreedy(
        coords, max_states=max_states, seed=42
    )

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
        "best_len": best_len,
    }


# ---------------------------------------------------------
# MAIN
# ---------------------------------------------------------

def main() -> None:
    energy = 0.5
    n_budget = 1000
    n_list = [5, 8, 10, 12, 15, 18, 20]

    print("==============================================================")
    print("=== TSP ANTI-GREEDY – STEP B (flusso rotto) ===================")
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

