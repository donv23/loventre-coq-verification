import math
from typing import List, Tuple

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

# Lista di energie da scandire (puoi cambiarla quando vuoi)
E_LIST: List[float] = [0.1, 0.2, 0.5, 1.0, 1.5, 2.0]


def analyze_energy_curve(name: str, n_budget: int, max_states: int = 1000) -> None:
    """
    Per una istanza SAT fissata:
      - calcola kappa_eff, entropy_eff, V0
      - per diverse energie E in E_LIST calcola:
          p_tunnel(E), E[N], P_success(N_budget)
          e la decisione Loventre corrispondente.
    """
    if name not in SAT_INSTANCES:
        print(f"[ERRORE] Istanza SAT '{name}' non trovata.")
        print("Istanze disponibili:", ", ".join(sorted(SAT_INSTANCES.keys())))
        return

    info = SAT_INSTANCES[name]
    cnf = info["cnf"]
    n_vars = info["n_vars"]

    # Geometria media sugli stati (non dipende da E)
    metrics_list = explore_instance(cnf, n_vars, max_states=max_states)
    kappa_eff, entropy_eff = aggregate_geometry(metrics_list)
    V0 = compute_potential(kappa_eff, entropy_eff, alpha=ALPHA_SAT, beta=BETA_SAT)

    print("===============================================================")
    print("=== Loventre SAT – Energy Curve per istanza specifica       ===")
    print("===============================================================")
    print(f"Istanza   : {name}")
    print(f"Descrizione: {info['description']}")
    print(f"n_vars    : {n_vars}")
    print(f"num_clauses: {len(cnf)}")
    print(f"N_budget  : {n_budget} tentativi meta")
    print()

    print(">>> GEOMETRIA INTERNA (media sugli stati)")
    print(f"  kappa_eff      : {kappa_eff:.3f}")
    print(f"  entropy_eff    : {entropy_eff:.3f}")
    print(f"  V0 (barriera)  : {V0:.4f}")
    print(f"  a_min (SAT)    : {A_MIN_SAT}")
    print()

    # Tabella energia → p_tunnel, EN, P_success, decisione
    header = (
        "E       p_tunnel(E)   E[N]          P_success    decision"
    )
    print(header)
    print("-" * len(header))

    for E in E_LIST:
        p = p_tunnel(V0, A_MIN_SAT, E)
        EN = expected_attempts(p)
        P_succ = success_probability(p, n_budget)
        dec_label, _ = decision_from_probability(P_succ)

        print(
            f"{E:5.2f}  "
            f"{p:11.3e}  "
            f"{EN:10.3e}  "
            f"{P_succ:10.3e}  "
            f"{dec_label}"
        )
    print()


def _parse_args() -> Tuple[str, int]:
    import sys

    name = "easy1"
    n_budget = 10000

    if len(sys.argv) >= 2:
        name = sys.argv[1].strip()

    if len(sys.argv) >= 3:
        try:
            n_budget = int(sys.argv[2])
        except ValueError:
            print("[ATTENZIONE] N_budget non numerico, uso 10000.")

    return name, n_budget


def main() -> None:
    name, n_budget = _parse_args()
    analyze_energy_curve(name, n_budget, max_states=1000)


if __name__ == "__main__":
    main()
