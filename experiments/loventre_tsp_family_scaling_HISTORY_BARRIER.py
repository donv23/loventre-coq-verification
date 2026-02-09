"""
STEP D1 — TSP HISTORY BARRIER
Vincolo globale che agisce DURANTE l’esplorazione:
la penalità cresce con la profondità se il path entra
in una regione geometricamente sfavorevole.
"""

import math
import random
from typing import List, Tuple, Dict

# =========================
# IMPORT LOCALI COERENTI
# =========================

from loventre_tsp_toy import (
    explore_tsp_instance,
)

# Import canonico robusto (pattern Loventre)
try:
    from loventre_tunneling import compute_potential, p_tunnel, expected_attempts
except ModuleNotFoundError:
    from metrics.loventre_tunneling import compute_potential, p_tunnel, expected_attempts


# =========================
# PARAMETRI STEP D1
# =========================

ALPHA_TSP = 1.0
BETA_TSP = 1.0
A_MIN_TSP = 4.0

HISTORY_PENALTY_WEIGHT = 0.6
DEPTH_EXPONENT = 1.3


# =========================
# GENERATORE TSP FAMILY
# =========================

def generate_tsp_coords_family(
    n_cities: int,
    radius: float = 1.0,
    seed: int = 0
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


# =========================
# HISTORY BARRIER
# =========================

def history_penalty(metrics: Dict[str, float]) -> float:
    depth_ratio = metrics["depth_ratio"]
    long_frac = metrics["long_frac"]
    tension = metrics["tension"]

    badness = 0.6 * long_frac + 0.4 * tension
    penalty = HISTORY_PENALTY_WEIGHT * badness * (depth_ratio ** DEPTH_EXPONENT)
    return min(1.0, penalty)


def curvature_with_history(metrics: Dict[str, float]) -> float:
    base_kappa = (
        0.35 * metrics["branch_ratio"]
        + 0.25 * metrics["long_frac"]
        + 0.25 * metrics["tension"]
        + 0.15 * metrics["depth_ratio"]
    )
    return max(0.0, min(1.0, base_kappa + history_penalty(metrics)))


def aggregate_geometry_with_history(
    metrics_list: List[Dict[str, float]]
) -> Tuple[float, float]:
    if not metrics_list:
        return 0.0, 0.0

    sum_k = 0.0
    sum_h = 0.0

    for m in metrics_list:
        sum_k += curvature_with_history(m)

        ps = m["short_frac"]
        pm = m["mid_frac"]
        pl = m["long_frac"]

        ent = 0.0
        for p in (ps, pm, pl):
            if p > 0.0:
                ent -= p * math.log(p)
        sum_h += ent / math.log(3.0)

    n = float(len(metrics_list))
    return sum_k / n, sum_h / n


# =========================
# FAMILY SCALING — STEP D1
# =========================

def success_probability(p: float, n_trials: int) -> float:
    if n_trials <= 0:
        return 0.0
    if p <= 0.0:
        return 0.0
    if p >= 1.0:
        return 1.0
    return 1.0 - math.exp(n_trials * math.log1p(-p))


def run_family_scaling(energy: float = 0.5, n_budget: int = 1000) -> None:
    n_list = [5, 8, 10, 12, 15, 18, 20]

    print("==============================================================")
    print("=== TSP HISTORY BARRIER – STEP D1 ============================")
    print("==============================================================")
    print(f"E = {energy}, N_budget = {n_budget}\n")

    header = (
        "n   kappa_eff  entropy_eff   V0      p_tunnel   E[N]     P_success"
    )
    print(header)
    print("-" * len(header))

    for n in n_list:
        coords = generate_tsp_coords_family(n, seed=42)
        metrics_list, _, _ = explore_tsp_instance(coords, max_states=80000)

        kappa_eff, entropy_eff = aggregate_geometry_with_history(metrics_list)
        V0 = compute_potential(kappa_eff, entropy_eff, ALPHA_TSP, BETA_TSP)
        p = p_tunnel(V0, A_MIN_TSP, energy)
        EN = expected_attempts(p)
        P = success_probability(p, n_budget)

        print(
            f"{n:2d}  "
            f"{kappa_eff:9.3f} "
            f"{entropy_eff:11.3f} "
            f"{V0:7.3f} "
            f"{p:9.3e} "
            f"{EN:8.2e} "
            f"{P:9.3e}"
        )


if __name__ == "__main__":
    run_family_scaling()

