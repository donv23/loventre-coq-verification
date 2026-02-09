import math
from typing import Dict, Any

from loventre_tunneling import compute_potential, p_tunnel, expected_attempts
from loventre_sat_toy import (
    SAT_INSTANCES,
    explore_instance,
    aggregate_geometry,
    ALPHA_SAT,
    BETA_SAT,
    A_MIN_SAT,
    success_probability,
    decision_from_probability,
)


def summarize_sat_instance(name: str, energy: float, n_budget: int, max_states: int = 1000) -> Dict[str, Any]:
    info = SAT_INSTANCES[name]
    cnf = info["cnf"]
    n_vars = info["n_vars"]

    metrics_list = explore_instance(cnf, n_vars, max_states=max_states)
    kappa_eff, entropy_eff = aggregate_geometry(metrics_list)

    V0 = compute_potential(kappa_eff, entropy_eff, alpha=ALPHA_SAT, beta=BETA_SAT)
    p = p_tunnel(V0, A_MIN_SAT, energy)
    expected_N = expected_attempts(p)
    P_succ = success_probability(p, n_budget)
    dec_label, dec_text = decision_from_probability(P_succ)

    return {
        "name": name,
        "description": info["description"],
        "n_vars": n_vars,
        "num_clauses": len(cnf),
        "kappa_eff": kappa_eff,
        "entropy_eff": entropy_eff,
        "V0": V0,
        "p_tunnel": p,
        "expected_N": expected_N,
        "P_success": P_succ,
        "decision_label": dec_label,
        "decision_text": dec_text,
    }


def main() -> None:
    import sys

    energy = 0.5
    n_budget = 10000

    if len(sys.argv) >= 2:
        try:
            energy = float(sys.argv[1])
        except ValueError:
            print("[ATTENZIONE] Energia non numerica, uso 0.5.")

    if len(sys.argv) >= 3:
        try:
            n_budget = int(sys.argv[2])
        except ValueError:
            print("[ATTENZIONE] N_budget non numerico, uso 10000.")

    print("===================================================================")
    print("=== Loventre SAT Portfolio – Panorama istanze interne           ===")
    print("===================================================================")
    print(f"Energia E   : {energy}")
    print(f"N_budget    : {n_budget} tentativi meta per istanza")
    print()

    header = (
        "name        n_vars  clauses  "
        "kappa_eff  entropy_eff   V0       "
        "p_tunnel(E)   P_success   decision"
    )
    print(header)
    print("-" * len(header))

    for name in sorted(SAT_INSTANCES.keys()):
        f = summarize_sat_instance(name, energy, n_budget, max_states=1000)
        print(
            f"{name:10s}  "
            f"{f['n_vars']:6d}  "
            f"{f['num_clauses']:7d}  "
            f"{f['kappa_eff']:9.3f}  "
            f"{f['entropy_eff']:11.3f}  "
            f"{f['V0']:7.4f}  "
            f"{f['p_tunnel']:11.3e}  "
            f"{f['P_success']:10.3e}  "
            f"{f['decision_label']}"
        )


if __name__ == "__main__":
    main()
