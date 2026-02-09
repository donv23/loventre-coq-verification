"""
loventre_meta_decision_lab.py

Dato un seed (param, factor), un livello di energia E e un budget di tentativi
N_budget, calcola:

  - p_tunnel(E)
  - E[N] = tentativi medi prima di un "lampo"
  - P_success = Probabilità di successo entro N_budget ≈ 1 - (1 - p)^N_budget
  - etichetta di difficoltà dal meta–engine
  - decisione operativa (conviene o no investire queste risorse)

Uso da terminale (esempi):

  python3 loventre_meta_decision_lab.py 1 1 0.5 10000
  python3 loventre_meta_decision_lab.py 2 2 0.5 10000
  python3 loventre_meta_decision_lab.py 2 3 0.5 10000
"""

import math
from typing import Tuple

from loventre_meta_engine import meta_analyze_seed
import loventre_seed_report as lsr


def success_probability(p: float, n_trials: int) -> float:
    """
    Probabilità di almeno un successo entro n_trials tentativi,
    con successo indipendente a probabilità p ad ogni tentativo:

      P_success = 1 - (1 - p)^n_trials

    Gestisce i casi estremi in modo robusto.
    """
    if n_trials <= 0:
        return 0.0
    if p <= 0.0:
        return 0.0
    if p >= 1.0:
        return 1.0

    # Usiamo log1p per stabilità numerica:
    # log((1-p)^n) = n * log(1-p)
    log_fail_one = math.log1p(-p)  # < 0
    log_fail_all = n_trials * log_fail_one

    # Se log_fail_all è molto negativo, (1-p)^n ~ 0
    if log_fail_all < -700.0:
        fail_all = 0.0
    else:
        fail_all = math.exp(log_fail_all)

    return max(0.0, min(1.0, 1.0 - fail_all))


def decision_from_probability(p_success: float) -> Tuple[str, str]:
    """
    Dato P_success, restituisce:

      - una etichetta sintetica
      - una raccomandazione testuale
    """
    if p_success >= 0.9:
        return (
            "Altamente raccomandato",
            "Investi tranquillamente queste risorse: la probabilità di successo è molto alta.",
        )
    if p_success >= 0.5:
        return (
            "Raccomandato",
            "Ha senso insistere: la probabilità di successo è ragionevole.",
        )
    if p_success >= 0.1:
        return (
            "Marginale",
            "Possibile ma rischioso: investi solo se il problema è prioritario.",
        )
    if p_success >= 0.01:
        return (
            "Molto rischioso",
            "Probabilità di successo molto bassa: valuta alternative o più energia.",
        )
    return (
        "Quasi impossibile",
        "Con questo budget e questa energia è praticamente inutile insistere.",
    )


def _parse_args() -> Tuple[int, int, float, int]:
    import sys

    # Default: seed critico canonico, stessa energia toy del seed_report, budget 10k
    param = lsr.DEFAULT_SEED_PARAM      # 2
    factor = lsr.DEFAULT_SEED_FACTOR    # 3
    energy = lsr.ENERGY_LEVEL           # es. 0.5
    n_budget = 10000

    if len(sys.argv) >= 3:
        try:
            param = int(sys.argv[1])
            factor = int(sys.argv[2])
        except ValueError:
            print("[ATTENZIONE] param/factor non numerici: uso default (2,3).")

    if len(sys.argv) >= 4:
        try:
            energy = float(sys.argv[3])
        except ValueError:
            print("[ATTENZIONE] energia non numerica: uso ENERGY_LEVEL di default.")

    if len(sys.argv) >= 5:
        try:
            n_budget = int(sys.argv[4])
        except ValueError:
            print("[ATTENZIONE] N_budget non numerico: uso 10000.")

    return param, factor, energy, n_budget


def main() -> None:
    param, factor, energy, n_budget = _parse_args()

    features = meta_analyze_seed(param, factor, energy)
    p = features["p_tunnel"]
    expected_N = features["expected_attempts"]
    p_success = success_probability(p, n_budget)
    dec_label, dec_text = decision_from_probability(p_success)

    print("===============================================================")
    print("=== Loventre Meta–Decision Lab                             ===")
    print("===============================================================")
    print(f"Seed        : (param={param}, factor={factor})")
    print(f"Energia E   : {energy}")
    print(f"N_budget    : {n_budget} tentativi")
    print()

    print(">>> STRUTTURA LOVENTRE")
    print(f"  region           : {features['region']}")
    print(f"  P_like / NP_like : P_like={features['P_like']}, NP_like={features['NP_like']}")
    print(f"  Pattern C        : {features['pattern_c']}")
    print(f"  Loventre Score   : {features['loventre_score']:.3f}")
    print(f"  difficulty_label : {features['difficulty_label']}")
    print(f"  difficulty_index : {features['difficulty_index']:.3f}")
    print()

    print(">>> TUNNELING A QUESTA ENERGIA")
    print(f"  V0 (barriera)    : {features['V0']:.4f}")
    print(f"  a_min (meta)     : {lsr.A_MIN_BARRIER}")
    print(f"  p_tunnel(E)      : {p:.3e}")
    print(f"  E[N] (tentativi) : {expected_N:.3e}")
    print()

    print(">>> PROBABILITÀ DI SUCCESSO ENTRO N_budget")
    print(f"  P_success        : {p_success:.3e}")
    print(f"  decision_label   : {dec_label}")
    print(f"  decision_text    : {dec_text}")
    print()


if __name__ == "__main__":
    main()
