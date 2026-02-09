"""
loventre_tsp_family_scaling.py

Esperimento di scala per una famiglia di problemi TSP_n.

Per una lista di n_cities (es. [5, 8, 10, 12, 15, 18]):

  - genera una istanza TSP strutturata ma pseudo–casuale,
  - esplora lo spazio dei tour con explore_tsp_instance (dal motore TSP toy),
  - aggrega la geometria interna (kappa_eff, entropy_eff),
  - calcola il potenziale V0 = ALPHA_TSP * kappa_eff + BETA_TSP * entropy_eff,
  - calcola p_tunnel(V0, A_MIN_TSP, E),
  - calcola E[N] e P_success(E, N_budget),
  - stampa una tabella che mostra come scala la difficoltà Loventre con n.

Uso:

  python3 loventre_tsp_family_scaling.py          # usa E=0.5, N_budget=1000
  python3 loventre_tsp_family_scaling.py 0.5 1000 # esplicito

"""

import math
import random
from typing import List, Tuple, Dict, Any

from loventre_tunneling import compute_potential, p_tunnel, expected_attempts
from loventre_tsp_toy import (
    explore_tsp_instance,
    aggregate_tsp_geometry,
    ALPHA_TSP,
    BETA_TSP,
    A_MIN_TSP,
)

# ---------------------------------------------------------
# 1. Utility comuni per probabilità di successo e decisioni
# ---------------------------------------------------------

def success_probability(p: float, n_trials: int) -> float:
    """Probabilità di almeno un successo in n_trials tentativi indipendenti."""
    if n_trials <= 0:
        return 0.0
    if p <= 0.0:
        return 0.0
    if p >= 1.0:
        return 1.0

    log_fail_one = math.log1p(-p)
    log_fail_all = n_trials * log_fail_one
    if log_fail_all < -700.0:
        fail_all = 0.0
    else:
        fail_all = math.exp(log_fail_all)
    return max(0.0, min(1.0, 1.0 - fail_all))


def decision_from_probability(p_success: float) -> str:
    """Etichetta qualitativa in base a P_success."""
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

def generate_tsp_coords_family(n_cities: int, radius: float = 1.0, seed: int = 0) -> List[Tuple[float, float]]:
    """
    Genera una istanza TSP_n:

    - distribuisce i punti quasi su una circonferenza,
    - aggiunge un piccolo rumore radiale e angolare,
    - usa un seed deterministico in funzione di n_cities.
    """
    rnd = random.Random(seed + 1000 * n_cities)
    coords: List[Tuple[float, float]] = []

    for i in range(n_cities):
        angle = 2.0 * math.pi * i / n_cities
        # r varia tra ~0.7 e 1.0 del raggio, con un po' di rumore
        r = radius * (0.7 + 0.3 * rnd.random())
        x = r * math.cos(angle) + 0.1 * (rnd.random() - 0.5)
        y = r * math.sin(angle) + 0.1 * (rnd.random() - 0.5)
        coords.append((x, y))

    return coords


def max_states_for_n(n_cities: int) -> int:
    """Heuristica per il numero massimo di stati da esplorare."""
    if n_cities <= 6:
        return 10000
    if n_cities <= 10:
        return 30000
    if n_cities <= 15:
        return 50000
    if n_cities <= 20:
        return 80000
    # oltre 20 città, teniamo un cap fisso (puoi modificare se necessario)
    return 100000


# ---------------------------------------------------------
# 3. Analisi di una singola istanza TSP_n
# ---------------------------------------------------------

def analyze_tsp_n(n_cities: int, energy: float, n_budget: int) -> Dict[str, Any]:
    """
    Costruisce una istanza TSP_n, esplora e calcola il profilo Loventre.
    """
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
    decision = decision_from_probability(P_succ)

    return {
        "n_cities": n_cities,
        "kappa_eff": kappa_eff,
        "entropy_eff": entropy_eff,
        "V0": V0,
        "p_tunnel": p,
        "EN": EN,
        "P_success": P_succ,
        "decision": decision,
        "best_length": best_length,
        "best_path": best_path,
        "max_states": max_states,
    }


# ---------------------------------------------------------
# 4. Esperimento di scala su una famiglia TSP_n
# ---------------------------------------------------------

def run_family_scaling(energy: float, n_budget: int) -> None:
    """
    Esegue la famiglia di TSP_n per una lista di n_cities predefinita.
    """
    n_list = [5, 8, 10, 12, 15, 18, 20, 25, 30]

    print("===================================================================")
    print("=== Loventre TSP Family Scaling – Famiglia di problemi TSP_n    ===")
    print("===================================================================")
    print(f"Energia E   : {energy}")
    print(f"N_budget    : {n_budget} tentativi meta per istanza")
    print(f"n_list      : {n_list}")
    print()

    header = (
        "n_cities  "
        "kappa_eff  entropy_eff   V0       "
        "p_tunnel(E)   E[N]          P_success   decision"
    )
    print(header)
    print("-" * len(header))

    for n_cities in n_list:
        res = analyze_tsp_n(n_cities, energy, n_budget)
        print(
            f"{res['n_cities']:8d}  "
            f"{res['kappa_eff']:9.3f} "
            f"{res['entropy_eff']:11.3f} "
            f"{res['V0']:7.4f}   "
            f"{res['p_tunnel']:11.3e} "
            f"{res['EN']:10.3e} "
            f"{res['P_success']:10.3e} "
            f"{res['decision']}"
        )

    print()
    print("Nota:")
    print("  - Se V0 cresce e p_tunnel(E) cala rapidamente con n,")
    print("    hai un segnale Loventre di 'barriera' che si irrobustisce con la taglia del problema.")
    print("  - Se, nonostante ciò, P_success con N_budget polinomiale resta alta,")
    print("    la famiglia è 'P-like' per il tuo motore alle risorse scelte.")
    print()


# ---------------------------------------------------------
# MAIN
# ---------------------------------------------------------

def _parse_args() -> Tuple[float, int]:
    import sys

    energy = 0.5
    n_budget = 1000

    if len(sys.argv) >= 2:
        try:
            energy = float(sys.argv[1])
        except ValueError:
            print("[ATTENZIONE] Energia non numerica, uso 0.5.")

    if len(sys.argv) >= 3:
        try:
            n_budget = int(sys.argv[2])
        except ValueError:
            print("[ATTENZIONE] N_budget non numerico, uso 1000.")

    return energy, n_budget


def main() -> None:
    energy, n_budget = _parse_args()
    run_family_scaling(energy, n_budget)


if __name__ == "__main__":
    main()