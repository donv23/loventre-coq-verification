"""
CSP CICLICO — Phase Transition Sweep (Loventre)
Variazione controllata di CYCLE_WEIGHT a n fisso.
"""

import math
import random
from typing import List, Dict, Tuple
from importlib.machinery import SourceFileLoader
from pathlib import Path

# ============================================================
# LOAD CANONICO loventre_tunneling.py (NO sys.path)
# ============================================================

ROOT = Path(__file__).resolve().parent.parent
TUNNELING_PATH = ROOT / "metrics" / "loventre_tunneling.py"

lov_tunnel = SourceFileLoader(
    "loventre_tunneling",
    str(TUNNELING_PATH)
).load_module()

compute_potential = lov_tunnel.compute_potential
p_tunnel = lov_tunnel.p_tunnel
expected_attempts = lov_tunnel.expected_attempts


# =========================
# PARAMETRI GLOBALI
# =========================

ALPHA = 1.0
BETA = 1.0
A_MIN = 4.0

N_FIXED = 14
E_FIXED = 0.5
N_BUDGET = 1000

# sweep del peso del ciclo
CYCLE_WEIGHTS = [0.0, 0.2, 0.4, 0.6, 0.8, 1.0, 1.2, 1.4, 1.6]


# =========================
# CSP CICLICO
# =========================

def generate_cyclic_csp(n: int, seed: int = 0) -> Dict:
    rnd = random.Random(seed + 1000 * n)
    constraints = []

    for i in range(n - 1):
        parity = rnd.randint(0, 1)
        constraints.append((i, i + 1, parity))

    cycle_parity = rnd.randint(0, 1)
    constraints.append((n - 1, 0, cycle_parity))

    return {"n": n, "constraints": constraints}


def explore_csp_states(csp: Dict, max_states: int = 60000) -> List[Dict[str, float]]:
    n = csp["n"]
    constraints = csp["constraints"]

    metrics = []
    stack = [({}, 0)]

    while stack and len(metrics) < max_states:
        assign, k = stack.pop()

        satisfied = 0
        violated = 0
        for (i, j, p) in constraints:
            if i in assign and j in assign:
                if (assign[i] ^ assign[j]) == p:
                    satisfied += 1
                else:
                    violated += 1

        depth_ratio = k / n if n > 0 else 0.0
        total = max(1, satisfied + violated)
        entropy = 1.0 - abs(0.5 - satisfied / total)

        cycle_pressure = 1.0 if (k == n - 1 and violated > 0) else 0.0

        metrics.append({
            "depth_ratio": depth_ratio,
            "entropy": entropy,
            "violated_frac": violated / total,
            "cycle_pressure": cycle_pressure,
        })

        if k >= n:
            continue

        for val in (0, 1):
            new_assign = dict(assign)
            new_assign[k] = val
            stack.append((new_assign, k + 1))

    return metrics


def aggregate_geometry(metrics: List[Dict[str, float]], cycle_weight: float) -> Tuple[float, float]:
    if not metrics:
        return 0.0, 0.0

    sum_k = 0.0
    sum_h = 0.0

    for m in metrics:
        kappa = (
            0.4 * m["violated_frac"]
            + 0.3 * m["entropy"]
            + 0.3 * m["cycle_pressure"] * cycle_weight
        )
        sum_k += min(1.0, kappa)
        sum_h += min(1.0, m["entropy"])

    n = len(metrics)
    return sum_k / n, sum_h / n


def success_probability(p: float, n_trials: int) -> float:
    if p <= 0.0:
        return 0.0
    if p >= 1.0:
        return 1.0
    return 1.0 - math.exp(n_trials * math.log1p(-p))


# =========================
# SWEEP DI FASE
# =========================

def run_phase_sweep() -> None:
    print("====================================================================")
    print("=== CSP CICLICO — PHASE TRANSITION (CYCLE_WEIGHT sweep) =============")
    print("====================================================================")
    print(f"n = {N_FIXED}, E = {E_FIXED}, N_budget = {N_BUDGET}\n")

    header = (
        "CYCLE_W   kappa_eff  entropy_eff   V0      "
        "p_tunnel     E[N]      P_success"
    )
    print(header)
    print("-" * len(header))

    csp = generate_cyclic_csp(N_FIXED, seed=42)
    metrics = explore_csp_states(csp, max_states=60000)

    for cw in CYCLE_WEIGHTS:
        kappa_eff, entropy_eff = aggregate_geometry(metrics, cw)
        V0 = compute_potential(kappa_eff, entropy_eff, ALPHA, BETA)
        p = p_tunnel(V0, A_MIN, E_FIXED)
        EN = expected_attempts(p)
        P = success_probability(p, N_BUDGET)

        print(
            f"{cw:7.2f}  "
            f"{kappa_eff:9.3f} "
            f"{entropy_eff:11.3f} "
            f"{V0:7.3f} "
            f"{p:11.3e} "
            f"{EN:9.2e} "
            f"{P:10.3e}"
        )


if __name__ == "__main__":
    run_phase_sweep()

