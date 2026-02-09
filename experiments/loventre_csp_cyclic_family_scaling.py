"""
CSP CICLICO — Family Scaling (Loventre)
Vincoli locali + ciclo globale ⇒ barriera informazionale.
"""

import math
import random
from typing import List, Dict, Tuple
from importlib.machinery import SourceFileLoader
from pathlib import Path

# ============================================================
# LOAD CANONICO loventre_tunneling.py (NO sys.path, NO package)
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
# PARAMETRI
# =========================

ALPHA = 1.0
BETA = 1.0
A_MIN = 4.0
CYCLE_WEIGHT = 0.9


# =========================
# MODELLO CSP CICLICO
# =========================

def generate_cyclic_csp(n: int, seed: int = 0) -> Dict:
    rnd = random.Random(seed + 1000 * n)
    constraints = []

    # vincoli locali
    for i in range(n - 1):
        parity = rnd.randint(0, 1)
        constraints.append((i, i + 1, parity))

    # ciclo globale
    cycle_parity = rnd.randint(0, 1)
    constraints.append((n - 1, 0, cycle_parity))

    return {"n": n, "constraints": constraints}


def explore_csp_states(csp: Dict, max_states: int = 50000) -> List[Dict[str, float]]:
    n = csp["n"]
    constraints = csp["constraints"]

    metrics = []
    stack = [({}, 0)]  # assignment, next_var

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


def aggregate_geometry(metrics: List[Dict[str, float]]) -> Tuple[float, float]:
    if not metrics:
        return 0.0, 0.0

    sum_k = 0.0
    sum_h = 0.0

    for m in metrics:
        kappa = (
            0.4 * m["violated_frac"]
            + 0.3 * m["entropy"]
            + 0.3 * m["cycle_pressure"] * CYCLE_WEIGHT
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


def run_family_scaling(E: float = 0.5, N_budget: int = 1000) -> None:
    n_list = [6, 8, 10, 12, 15, 18]

    print("==============================================================")
    print("=== CSP CICLICO – Family Scaling =============================")
    print("==============================================================")
    print(f"E = {E}, N_budget = {N_budget}\n")

    header = "n  kappa_eff  entropy_eff   V0      p_tunnel   E[N]     P_success"
    print(header)
    print("-" * len(header))

    for n in n_list:
        csp = generate_cyclic_csp(n, seed=42)
        metrics = explore_csp_states(csp, max_states=60000)

        kappa_eff, entropy_eff = aggregate_geometry(metrics)
        V0 = compute_potential(kappa_eff, entropy_eff, ALPHA, BETA)
        p = p_tunnel(V0, A_MIN, E)
        EN = expected_attempts(p)
        P = success_probability(p, N_budget)

        print(
            f"{n:2d} "
            f"{kappa_eff:9.3f} "
            f"{entropy_eff:11.3f} "
            f"{V0:7.3f} "
            f"{p:9.3e} "
            f"{EN:8.2e} "
            f"{P:9.3e}"
        )


if __name__ == "__main__":
    run_family_scaling()

