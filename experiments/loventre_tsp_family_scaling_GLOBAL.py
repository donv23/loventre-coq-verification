"""
loventre_tsp_family_scaling_GLOBAL.py

STEP C – TSP con vincolo globale non locale.
Introduciamo una penalità di cluster-ordering.
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
# TSP GEOMETRICO + CLUSTER
# ---------------------------------------------------------

def generate_clustered_coords(n: int, radius: float = 1.0) -> Tuple[List[Tuple[float, float]], List[int]]:
    """
    Genera città su circonferenza.
    Prime n//2 = cluster A (0), restanti = cluster B (1).
    """
    coords = []
    clusters = []
    for i in range(n):
        angle = 2.0 * math.pi * i / n
        coords.append((radius * math.cos(angle), radius * math.sin(angle)))
        clusters.append(0 if i < n // 2 else 1)
    return coords, clusters


# ---------------------------------------------------------
# VINCOLO GLOBALE
# ---------------------------------------------------------

def global_cluster_penalty(path: List[int], clusters: List[int], penalty: float = 5.0) -> float:
    """
    Penalità globale:
    se il path visita cluster A dopo essere entrato in B → penalità.
    """
    seen_B = False
    for city in path:
        if clusters[city] == 1:
            seen_B = True
        elif clusters[city] == 0 and seen_B:
            return penalty
    return 0.0


# ---------------------------------------------------------
# DFS CON PENALITÀ GLOBALE
# ---------------------------------------------------------

def explore_tsp_instance_global(
    coords: List[Tuple[float, float]],
    clusters: List[int],
    max_states: int = 50000,
) -> Tuple[List[Dict[str, float]], float]:

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
            base_len = cur_len + dist[path[-1]][path[0]]
            penalty = global_cluster_penalty(path, clusters)
            tour_len = base_len + penalty

            if best_length is None or tour_len < best_length:
                best_length = tour_len
            continue

        last = path[-1]
        candidates = [c for c in range(n) if not (mask & (1 << c))]
        random.shuffle(candidates)

        for c in candidates:
            stack.append(
                (path + [c], mask | (1 << c), cur_len + dist[last][c])
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
    coords, clusters = generate_clustered_coords(n)
    max_states = max_states_for_n(n)

    metrics_list, best_len = explore_tsp_instance_global(
        coords, clusters, max_states=max_states
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
    print("=== TSP GLOBAL – STEP C (vincolo non locale) =================")
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

