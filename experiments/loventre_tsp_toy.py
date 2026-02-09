"""
loventre_tsp_toy.py

Motore TSP toy per il Loventre Engine.
"""

# ---------------------------------------------------------
# BOOTSTRAP PATH CANONICO
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
from typing import List, Tuple, Dict, Any

from metrics.loventre_tunneling import compute_potential, p_tunnel, expected_attempts

# ============================================================
# PARAMETRI FISICI CANONICI (TSP)
# ============================================================

ALPHA_TSP = 1.0
BETA_TSP = 1.0
A_MIN_TSP = 4.0   # spessore minimo barriera TSP

# ============================================================
# 1. Istanze TSP toy
# ============================================================

CityCoord = Tuple[float, float]

TSP_INSTANCES: Dict[str, Dict[str, Any]] = {
    "tsp5": {
        "description": "TSP con 5 città in configurazione quasi pentagonale",
        "coords": [
            (0.0, 0.0),
            (1.0, 0.0),
            (1.0, 1.0),
            (0.0, 1.0),
            (0.5, 1.7),
        ],
    },
    "tsp10": {
        "description": "TSP con 10 città su griglia 3x3 + un punto superiore",
        "coords": [
            (0.0, 0.0),
            (1.0, 0.0),
            (2.0, 0.0),
            (0.0, 1.0),
            (1.0, 1.0),
            (2.0, 1.0),
            (0.0, 2.0),
            (1.0, 2.0),
            (2.0, 2.0),
            (1.0, 3.0),
        ],
    },
}

# ============================================================
# 2. Distanze e statistiche
# ============================================================

def build_distance_matrix(coords: List[CityCoord]) -> List[List[float]]:
    n = len(coords)
    dist = [[0.0] * n for _ in range(n)]
    for i in range(n):
        xi, yi = coords[i]
        for j in range(i + 1, n):
            xj, yj = coords[j]
            d = math.hypot(xi - xj, yi - yj)
            dist[i][j] = d
            dist[j][i] = d
    return dist


def compute_distance_stats(coords: List[CityCoord]) -> Dict[str, Any]:
    dist = build_distance_matrix(coords)
    n = len(coords)
    edges: List[float] = []

    for i in range(n):
        for j in range(i + 1, n):
            edges.append(dist[i][j])

    edges.sort()
    if not edges:
        mean_edge = thr_short = thr_long = 0.0
    else:
        mean_edge = sum(edges) / len(edges)

        def percentile(q: float) -> float:
            idx = int((len(edges) - 1) * q)
            return edges[idx]

        thr_short = percentile(0.33)
        thr_long = percentile(0.66)

    return {
        "dist": dist,
        "n_cities": n,
        "mean_edge": mean_edge,
        "thr_short": thr_short,
        "thr_long": thr_long,
    }

# ============================================================
# 3. Metriche TSP
# ============================================================

def compute_tsp_state_metrics(
    path: List[int],
    current_length: float,
    stats: Dict[str, Any],
) -> Dict[str, float]:
    dist = stats["dist"]
    n = stats["n_cities"]
    mean_edge = stats["mean_edge"]
    thr_short = stats["thr_short"]
    thr_long = stats["thr_long"]

    depth = len(path)
    n_edges = max(0, depth - 1)

    short_cnt = mid_cnt = long_cnt = 0

    if n_edges > 0:
        for i in range(depth - 1):
            d = dist[path[i]][path[i + 1]]
            if d <= thr_short:
                short_cnt += 1
            elif d >= thr_long:
                long_cnt += 1
            else:
                mid_cnt += 1

    total = max(1, n_edges)
    frac_short = short_cnt / total
    frac_mid = mid_cnt / total
    frac_long = long_cnt / total

    remaining = n - depth
    branch_ratio = remaining / (n - 1) if n > 1 else 0.0
    depth_ratio = depth / n if n > 0 else 0.0

    if n_edges > 0 and mean_edge > 0.0:
        avg_edge = current_length / n_edges
        tension = min(1.0, abs(avg_edge - mean_edge) / mean_edge)
    else:
        tension = 0.0

    return {
        "branch_ratio": branch_ratio,
        "depth_ratio": depth_ratio,
        "short_frac": frac_short,
        "mid_frac": frac_mid,
        "long_frac": frac_long,
        "tension": tension,
    }


def curvature_of_tsp_state(m: Dict[str, float]) -> float:
    raw = (
        0.35 * m["branch_ratio"]
        + 0.25 * m["long_frac"]
        + 0.25 * m["tension"]
        + 0.15 * m["depth_ratio"]
    )
    return max(0.0, min(1.0, raw))


def entropy_of_tsp_state(m: Dict[str, float]) -> float:
    ent = 0.0
    for p in (m["short_frac"], m["mid_frac"], m["long_frac"]):
        if p > 0.0:
            ent -= p * math.log(p)
    return ent / math.log(3.0) if ent > 0.0 else 0.0


def aggregate_tsp_geometry(metrics_list: List[Dict[str, float]]) -> Tuple[float, float]:
    if not metrics_list:
        return 0.0, 0.0
    return (
        sum(curvature_of_tsp_state(m) for m in metrics_list) / len(metrics_list),
        sum(entropy_of_tsp_state(m) for m in metrics_list) / len(metrics_list),
    )

# ============================================================
# 4. Esplorazione DFS limitata
# ============================================================

def explore_tsp_instance(
    coords: List[CityCoord],
    max_states: int = 50000,
) -> Tuple[List[Dict[str, float]], float, List[int]]:
    stats = compute_distance_stats(coords)
    dist = stats["dist"]
    n = stats["n_cities"]

    metrics_list: List[Dict[str, float]] = []
    best_length: float | None = None
    best_path: List[int] | None = None

    stack = [([0], 1 << 0, 0.0)]

    while stack and len(metrics_list) < max_states:
        path, mask, cur_len = stack.pop()
        metrics_list.append(compute_tsp_state_metrics(path, cur_len, stats))

        if len(path) == n:
            tour_len = cur_len + dist[path[-1]][path[0]]
            if best_length is None or tour_len < best_length:
                best_length = tour_len
                best_path = path
            continue

        last = path[-1]
        candidates = [
            (dist[last][c], c)
            for c in range(n)
            if not (mask & (1 << c))
        ]
        candidates.sort(reverse=True)

        for _, c in candidates:
            stack.append(
                (path + [c], mask | (1 << c), cur_len + dist[last][c])
            )

    if best_length is None:
        return metrics_list, math.inf, []

    return metrics_list, best_length, best_path

