from typing import List

from loventre_tsp_critical_family_scaling import (
    CRITICAL_N_LIST as TSP_CRIT_N_LIST,
    CRITICAL_SIGNATURES as TSP_CRIT_SIGNATURES,
    barrier_height as tsp_barrier_height,
    barrier_thickness as tsp_barrier_thickness,
    tunneling_probability as tsp_tunneling_probability,
    expected_attempts as tsp_expected_attempts,
    success_probability as tsp_success_probability,
    decision_label as tsp_decision_label,
)

from loventre_sat_critical_family_scaling import (
    CRITICAL_SAT_LIST as SAT_CRIT_LIST,
    CRITICAL_SAT_SIGNATURES as SAT_CRIT_SIGNATURES,
    barrier_height as sat_barrier_height,
    barrier_thickness as sat_barrier_thickness,
    tunneling_probability as sat_tunneling_probability,
    expected_attempts as sat_expected_attempts,
    success_probability as sat_success_probability,
    decision_label as sat_decision_label,
)


def print_tsp_block_for_energy(energy: float, n_budget: int) -> None:
    """
    Stampa la tabella TSP_crit_n per una data energia E e N_budget.
    """
    print()
    print(f"--- TSP_crit_n – Energia E = {energy:.3f} ---")
    print("n_cities  kappa_eff  entropy_eff   V0       a_min   p_tunnel(E)   E[N]          P_success   decision")
    print("---------------------------------------------------------------------------------------------------")

    for n_cities in TSP_CRIT_N_LIST:
        sig = TSP_CRIT_SIGNATURES[n_cities]
        kappa_eff = sig["kappa_eff"]
        entropy_eff = sig["entropy_eff"]

        V0 = tsp_barrier_height(kappa_eff, entropy_eff)
        a_min = tsp_barrier_thickness(n_cities)
        p_t = tsp_tunneling_probability(V0, a_min, energy)
        e_n = tsp_expected_attempts(p_t)
        p_s = tsp_success_probability(p_t, n_budget)
        label = tsp_decision_label(p_s)

        print(
            f"{n_cities:7d}  "
            f"{kappa_eff:8.3f}  "
            f"{entropy_eff:8.3f}  "
            f"{V0:6.4f}  "
            f"{a_min:6.2f}  "
            f"{p_t:11.3e}  "
            f"{e_n:11.3e}  "
            f"{p_s:9.3e} {label}"
        )


def print_sat_block_for_energy(energy: float, n_budget: int) -> None:
    """
    Stampa la tabella SAT_crit_n per una data energia E e N_budget.
    """
    print()
    print(f"--- SAT_crit_n – Energia E = {energy:.3f} ---")
    print("name        n_vars  clauses  kappa_eff  entropy_eff   V0       a_min   p_tunnel(E)   E[N]          P_success   decision")
    print("------------------------------------------------------------------------------------------------------------------------")

    for name in SAT_CRIT_LIST:
        sig = SAT_CRIT_SIGNATURES[name]
        n_vars = sig["n_vars"]
        num_clauses = sig["num_clauses"]
        kappa_eff = sig["kappa_eff"]
        entropy_eff = sig["entropy_eff"]

        V0 = sat_barrier_height(kappa_eff, entropy_eff)
        a_min = sat_barrier_thickness(name)
        p_t = sat_tunneling_probability(V0, a_min, energy)
        e_n = sat_expected_attempts(p_t)
        p_s = sat_success_probability(p_t, n_budget)
        label = sat_decision_label(p_s)

        print(
            f"{name:10s}  "
            f"{n_vars:6d}  "
            f"{num_clauses:7d}  "
            f"{kappa_eff:8.3f}  "
            f"{entropy_eff:8.3f}  "
            f"{V0:6.4f}  "
            f"{a_min:6.2f}  "
            f"{p_t:11.3e}  "
            f"{e_n:11.3e}  "
            f"{p_s:9.3e} {label}"
        )


def run_phase_diagram(energies: List[float], n_budget: int) -> None:
    """
    Phase diagram Loventre per le famiglie critiche:
      - TSP_crit_n (tour)
      - SAT_crit_n (formule)

    Per ogni energia E in energies:
      - stampa un blocco TSP_crit_n(E),
      - stampa un blocco SAT_crit_n(E).
    """
    print()
    print("===================================================================")
    print("=== LOVENTRE PHASE DIAGRAM – Famiglie critiche SAT/TSP         ===")
    print("===================================================================")
    print(f"Energia list : {energies}")
    print(f"N_budget     : {n_budget} tentativi meta per istanza")
    print()

    for E in energies:
        print()
        print("###################################################################")
        print(f"### ENERGIA E = {E:.3f}")
        print("###################################################################")
        print_tsp_block_for_energy(E, n_budget)
        print_sat_block_for_energy(E, n_budget)


def main():
    # Energies di prova per il diagramma di fase
    energies = [0.2, 0.3, 0.5, 0.7, 1.0]
    # Budget fisso (puoi cambiarlo se vuoi fare altri esperimenti)
    n_budget = 1000

    run_phase_diagram(energies, n_budget)


if __name__ == "__main__":
    main()
