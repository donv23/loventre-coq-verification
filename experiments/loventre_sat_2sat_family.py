from typing import Dict, Any

from loventre_tunneling import compute_potential, p_tunnel, expected_attempts
from loventre_sat_toy import (
    CNF,
    explore_instance,
    aggregate_geometry,
    ALPHA_SAT,
    BETA_SAT,
    A_MIN_SAT,
    success_probability,
    decision_from_probability,
)


# ============================================================
# Loventre 2-SAT Family – Seed v3 (Dicembre 2025)
# ============================================================
#
# Questo modulo definisce una mini–famiglia di istanze 2-SAT
# da usare come base per:
#   - costruire i witness JSON metrics_2SAT_easy_demo.json
#     e metrics_2SAT_crit_demo.json;
#   - esplorare la geometria Loventre (kappa_eff, entropy_eff)
#     in regime "molto sotto soglia" vs "vicino alla soglia";
#   - dare spessore operativo alle classi P_like e Pacc_Lov
#     nel dominio SAT.
#
# NOTA: qui NON costruiamo ancora i metrics_*.json; questo
# modulo è una fixture geometrica/storica che verrà poi
# usata da uno script di pipeline/builder dedicato.
# ============================================================


TWO_SAT_FAMILY: Dict[str, Dict[str, Any]] = {
    # --------------------------------------------------------
    # Istanza "molto sotto soglia" – facile, P_like SAFE/LOW.
    # --------------------------------------------------------
    "2SAT_easy_demo": {
        "description": (
            "2-SAT easy: formula molto sotto soglia, poche clausole, "
            "ampio spazio di assegnazioni soddisfacenti."
        ),
        "n_vars": 6,
        # Solo clausole di lunghezza 1 o 2 → 2-SAT.
        "cnf": [
            [1, 2],
            [3],
            [4, 5],
            [6],
            [2, 3],
        ],
        # Hint semantici per integrazione futura nella pipeline:
        "regime_hint": "easy_subcritical",
        "metrics_target": "metrics_2SAT_easy_demo.json",
        "target_meta_label": "meta_P_like_like",
        "target_risk_class": "risk_LOW",
        "target_global_decision": "GD_safe",
        "target_global_color": "GC_green",
    },
    # --------------------------------------------------------
    # Istanza "vicino alla soglia" – ancora in P, Pacc_Lov.
    # --------------------------------------------------------
    "2SAT_crit_demo": {
        "description": (
            "2-SAT crit: formula vicina alla soglia di soddisfacibilità, "
            "struttura più densa e vincoli intrecciati."
        ),
        "n_vars": 12,
        "cnf": [
            [1, 2],
            [-1, 3],
            [2, -3],
            [3, 4],
            [-4, 5],
            [5, 6],
            [-5, -6],
            [6, 7],
            [-2, 7],
            [7, 8],
            [-7, -8],
            [8, 9],
            [-8, 10],
            [10, -9],
            [11, 12],
            [-11, -12],
        ],
        "regime_hint": "critical_accessible",
        "metrics_target": "metrics_2SAT_crit_demo.json",
        "target_meta_label": "meta_P_like_accessible",
        "target_risk_class": "risk_LOW",  # ancora non NP_like_black_hole
        "target_global_decision": "GD_borderline",
        "target_global_color": "GC_green",  # borderline green
    },
}


def list_2sat_instances() -> Dict[str, Dict[str, Any]]:
    """
    Restituisce il dizionario completo della famiglia 2-SAT.

    Viene esposto come funzione per evitare che altri moduli
    si appoggino direttamente alla variabile globale e per
    mantenere un minimo di controllo sul "contratto" interno.
    """
    return dict(TWO_SAT_FAMILY)


def summarize_2sat_instance(
    name: str,
    energy: float,
    n_budget: int,
    max_states: int = 2000,
) -> Dict[str, Any]:
    """
    Applica la geometria Loventre (come in loventre_sat_toy) a una istanza 2-SAT.

    Usa:
      - explore_instance / aggregate_geometry per kappa_eff, entropy_eff;
      - compute_potential + p_tunnel + expected_attempts;
      - success_probability + decision_from_probability.

    Ritorna un dizionario con:
      - parametri strutturali (n_vars, num_clauses)
      - kappa_eff, entropy_eff, V0, p_tunnel, E[N], P_success
      - decision_label, decision_text
      - hint semantici di target (meta_label, risk_class, ecc.).
    """
    family = list_2sat_instances()
    if name not in family:
        raise KeyError(f"Istanza 2-SAT '{name}' non definita nel seed 2-SAT.")

    info = family[name]
    cnf: CNF = info["cnf"]
    n_vars: int = info["n_vars"]

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
        "regime_hint": info.get("regime_hint"),
        "metrics_target": info.get("metrics_target"),
        "target_meta_label": info.get("target_meta_label"),
        "target_risk_class": info.get("target_risk_class"),
        "target_global_decision": info.get("target_global_decision"),
        "target_global_color": info.get("target_global_color"),
    }


def _parse_args():
    """
    Parsing semplice da linea di comando.

    Uso:
        python3 loventre_sat_2sat_family.py [istanza] [E] [N_budget]

    Default:
        istanza  = "2SAT_easy_demo"
        E        = 0.5
        N_budget = 10000
    """
    import sys

    name = "2SAT_easy_demo"
    energy = 0.5
    n_budget = 10000

    if len(sys.argv) >= 2:
        candidate = sys.argv[1].strip()
        if candidate:
            name = candidate

    if len(sys.argv) >= 3:
        try:
            energy = float(sys.argv[2])
        except ValueError:
            print("[ATTENZIONE] Energia non numerica, uso 0.5.")

    if len(sys.argv) >= 4:
        try:
            n_budget = int(sys.argv[3])
        except ValueError:
            print("[ATTENZIONE] N_budget non numerico, uso 10000.")

    return name, energy, n_budget


def main() -> None:
    name, energy, n_budget = _parse_args()

    print("===================================================================")
    print("=== Loventre 2-SAT Family – Esplorazione geometrica preliminare ===")
    print("===================================================================")
    print(f"Istanza  : {name}")
    print(f"Energia E: {energy}")
    print(f"N_budget : {n_budget} tentativi meta")
    print()

    try:
        summary = summarize_2sat_instance(name, energy, n_budget, max_states=2000)
    except KeyError as e:
        print(f"[ERRORE] {e}")
        print("Istanze disponibili:", ", ".join(sorted(list_2sat_instances().keys())))
        return

    print(">>> STRUTTURA 2-SAT")
    print(f"  n_vars      : {summary['n_vars']}")
    print(f"  num_clauses : {summary['num_clauses']}")
    print()

    print(">>> GEOMETRIA LOVENTRE (media sugli stati visitati)")
    print(f"  kappa_eff   : {summary['kappa_eff']:.3f}")
    print(f"  entropy_eff : {summary['entropy_eff']:.3f}")
    print(f"  V0          : {summary['V0']:.4f}")
    print(f"  a_min (SAT) : {A_MIN_SAT}")
    print()

    print(">>> TUNNELING E PROBABILITÀ DI SUCCESSO")
    print(f"  p_tunnel(E) : {summary['p_tunnel']:.3e}")
    print(f"  E[N]        : {summary['expected_N']:.3e}")
    print(f"  P_success   : {summary['P_success']:.3e}")
    print(f"  decision    : {summary['decision_label']}")
    print(f"  nota        : {summary['decision_text']}")
    print()

    print(">>> HINT DI TARGET (per integrazione futura nel metrics bus)")
    print(f"  regime_hint           : {summary['regime_hint']}")
    print(f"  metrics_target        : {summary['metrics_target']}")
    print(f"  target_meta_label     : {summary['target_meta_label']}")
    print(f"  target_risk_class     : {summary['target_risk_class']}")
    print(f"  target_global_decision: {summary['target_global_decision']}")
    print(f"  target_global_color   : {summary['target_global_color']}")
    print()


if __name__ == "__main__":
    main()

