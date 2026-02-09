import math
from typing import Dict, List, Tuple

from loventre_tunneling import compute_potential, p_tunnel, expected_attempts


# ============================================================
# 1. Rappresentazione di un problema SAT in CNF
# ============================================================

# Clausola = lista di interi (es. [1, -2, 3] = x1 OR ¬x2 OR x3)
Clause = List[int]
CNF = List[Clause]


# Alcune istanze toy interne (per ora hard-coded)
SAT_INSTANCES = {
    "easy1": {
        "description": "Formula banale con clausole unitarie positive",
        "n_vars": 3,
        "cnf": [
            [1],
            [2],
            [3],
        ],
    },
    "mixed1": {
        "description": "Formula piccola con interazioni semplici",
        "n_vars": 3,
        "cnf": [
            [1, 2],
            [-1, 2],
            [1, -2],
        ],
    },
    "hard1": {
        "description": "Formula un po' più strutturata su 4 variabili",
        "n_vars": 4,
        "cnf": [
            [1, 2, -3],
            [-1, 3],
            [-2, 4],
            [-3, -4],
            [2, 3, 4],
        ],
    },
}


# ============================================================
# 2. Valutazione di una clausola e metriche di stato
# ============================================================

def eval_clause(clause: Clause, assignment: Dict[int, bool]) -> int:
    """
    Valuta una clausola sotto una assegnazione parziale.

    Ritorna:
      +1 se la clausola è già soddisfatta,
      -1 se è insoddisfatta (tutti i letterali assegnati e falsi),
       0 se è ancora "aperta" (nessun letterale ancora vero, almeno uno non assegnato).
    """
    has_unassigned = False
    for lit in clause:
        var = abs(lit)
        val = assignment.get(var)
        if val is None:
            has_unassigned = True
        else:
            if (lit > 0 and val) or (lit < 0 and (not val)):
                return 1  # soddisfatta
    if has_unassigned:
        return 0  # aperta
    return -1     # insoddisfatta


def compute_state_metrics(cnf: CNF, assignment: Dict[int, bool], n_vars: int) -> Dict[str, float]:
    """
    Calcola metriche strutturali per lo stato corrente del solver SAT.

    Restituisce un dizionario con:
      - n_vars
      - depth
      - num_clauses
      - num_satisfied
      - num_unsatisfied
      - num_open
      - unit_open: numero di clausole aperte con esattamente 1 letterale non assegnato
    """
    num_clauses = len(cnf)
    num_satisfied = 0
    num_unsatisfied = 0
    num_open = 0
    unit_open = 0

    for clause in cnf:
        status = eval_clause(clause, assignment)
        if status == 1:
            num_satisfied += 1
        elif status == -1:
            num_unsatisfied += 1
        else:
            num_open += 1
            # Contiamo quanti letterali non assegnati ha la clausola
            unassigned = 0
            for lit in clause:
                var = abs(lit)
                if assignment.get(var) is None:
                    unassigned += 1
            if unassigned == 1:
                unit_open += 1

    depth = len(assignment)

    return {
        "n_vars": float(n_vars),
        "depth": float(depth),
        "num_clauses": float(num_clauses),
        "num_satisfied": float(num_satisfied),
        "num_unsatisfied": float(num_unsatisfied),
        "num_open": float(num_open),
        "unit_open": float(unit_open),
    }


# ============================================================
# 3. Curvatura e entropia di uno stato SAT
# ============================================================

def curvature_of_state(metrics: Dict[str, float]) -> float:
    """
    Definisce una 'curvatura' toy per uno stato SAT, in [0,1]:

      - conflict_ratio: frazione di clausole insoddisfatte (conflitti puri)
      - unit_ratio    : frazione di clausole aperte che sono unitarie (vincoli stretti)
      - depth_norm    : profondità relativa nell'albero di ricerca

    kappa = 0.5 * conflict_ratio + 0.3 * unit_ratio + 0.2 * depth_norm
    (clippata in [0,1]).
    """
    num_clauses = metrics["num_clauses"]
    if num_clauses <= 0:
        return 0.0

    conflict_ratio = metrics["num_unsatisfied"] / num_clauses
    num_open = metrics["num_open"]
    if num_open > 0:
        unit_ratio = metrics["unit_open"] / num_open
    else:
        unit_ratio = 0.0

    n_vars = metrics["n_vars"]
    if n_vars > 0:
        depth_norm = metrics["depth"] / n_vars
    else:
        depth_norm = 0.0

    raw = 0.5 * conflict_ratio + 0.3 * unit_ratio + 0.2 * depth_norm
    return max(0.0, min(1.0, raw))


def entropy_of_state(metrics: Dict[str, float]) -> float:
    """
    Entropia normalizzata della tripla:

      (frazione di clausole soddisfatte,
       frazione di clausole insoddisfatte,
       frazione di clausole aperte)

    Normalizzata in [0,1] dividendo per log(3).
    """
    num_clauses = metrics["num_clauses"]
    if num_clauses <= 0:
        return 0.0

    ps = metrics["num_satisfied"] / num_clauses
    pu = metrics["num_unsatisfied"] / num_clauses
    po = metrics["num_open"] / num_clauses

    ent = 0.0
    for p in (ps, pu, po):
        if p > 0.0:
            ent -= p * math.log(p)

    norm = math.log(3.0)
    if norm <= 0.0:
        return 0.0
    H = ent / norm
    return max(0.0, min(1.0, H))


# ============================================================
# 4. Esplorazione DFS dello spazio SAT (per campionare stati)
# ============================================================

def explore_instance(cnf: CNF, n_vars: int, max_states: int = 1000) -> List[Dict[str, float]]:
    """
    Esegue una DFS limitata nello spazio delle assegnazioni per il CNF dato,
    con un massimo di max_states stati visitati.

    Restituisce una lista di metriche di stato.
    """
    metrics_list: List[Dict[str, float]] = []

    # Stack per DFS iterativa: (assignment, next_var)
    stack: List[Tuple[Dict[int, bool], int]] = [({}, 1)]

    while stack and len(metrics_list) < max_states:
        assignment, next_var = stack.pop()

        m = compute_state_metrics(cnf, assignment, n_vars)
        metrics_list.append(m)

        # Se c'è già un conflitto, non espandiamo oltre questo ramo
        if m["num_unsatisfied"] > 0:
            continue

        # Se abbiamo assegnato tutte le variabili, non espandiamo
        if next_var > n_vars:
            continue

        # Altrimenti, espandiamo due rami: var = True e var = False
        assign_true = assignment.copy()
        assign_true[next_var] = True
        assign_false = assignment.copy()
        assign_false[next_var] = False

        # DFS: pushiamo prima il ramo False, così True viene esplorato prima
        stack.append((assign_false, next_var + 1))
        stack.append((assign_true, next_var + 1))

    return metrics_list


def aggregate_geometry(metrics_list: List[Dict[str, float]]) -> Tuple[float, float]:
    """
    Dato un insieme di stati visitati, calcola kappa_eff e entropy_eff
    come medie delle curvature e entropie dei singoli stati.
    """
    if not metrics_list:
        return 0.0, 0.0

    kappas = []
    entropies = []
    for m in metrics_list:
        kappas.append(curvature_of_state(m))
        entropies.append(entropy_of_state(m))

    kappa_eff = sum(kappas) / len(kappas)
    entropy_eff = sum(entropies) / len(entropies)
    return kappa_eff, entropy_eff


# ============================================================
# 5. Probabilità di successo entro N tentativi e decisione
# ============================================================

def success_probability(p: float, n_trials: int) -> float:
    """
    Probabilità di almeno un successo entro n_trials tentativi,
    con probabilità p per tentativo:

      P_success = 1 - (1 - p)^n_trials
    """
    if n_trials <= 0:
        return 0.0
    if p <= 0.0:
        return 0.0
    if p >= 1.0:
        return 1.0

    log_fail_one = math.log1p(-p)        # log(1-p) < 0
    log_fail_all = n_trials * log_fail_one

    if log_fail_all < -700.0:
        fail_all = 0.0
    else:
        fail_all = math.exp(log_fail_all)

    return max(0.0, min(1.0, 1.0 - fail_all))


def decision_from_probability(p_success: float) -> Tuple[str, str]:
    """
    Dato P_success, restituisce:
      - etichetta sintetica
      - raccomandazione testuale
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


# ============================================================
# 6. Analisi completa di una istanza SAT con il motore Loventre
# ============================================================

ALPHA_SAT = 1.0
BETA_SAT = 1.0
A_MIN_SAT = 4.0  # per ora usiamo lo stesso a_min del toy seed grid


def analyze_sat_instance(name: str, energy: float, n_budget: int, max_states: int = 1000) -> None:
    """
    Analizza una istanza SAT interna usando la geometria Loventre:

      - esplora lo spazio di ricerca (DFS limitata)
      - calcola kappa_eff, entropy_eff
      - costruisce V0, p_tunnel, E[N]
      - stima P_success entro n_budget
      - produce una raccomandazione
    """
    if name not in SAT_INSTANCES:
        print(f"[ERRORE] Istanza SAT '{name}' non trovata.")
        print("Istanze disponibili:", ", ".join(SAT_INSTANCES.keys()))
        return

    info = SAT_INSTANCES[name]
    cnf = info["cnf"]
    n_vars = info["n_vars"]

    print("===============================================================")
    print("=== Loventre SAT Toy – Analisi di una istanza SAT           ===")
    print("===============================================================")
    print(f"Istanza   : {name}")
    print(f"Descrizione: {info['description']}")
    print(f"n_vars    : {n_vars}")
    print(f"num_clauses: {len(cnf)}")
    print(f"Energia E : {energy}")
    print(f"N_budget  : {n_budget} tentativi meta")
    print()

    metrics_list = explore_instance(cnf, n_vars, max_states=max_states)
    kappa_eff, entropy_eff = aggregate_geometry(metrics_list)

    V0 = compute_potential(kappa_eff, entropy_eff, alpha=ALPHA_SAT, beta=BETA_SAT)
    p = p_tunnel(V0, A_MIN_SAT, energy)
    expected_N = expected_attempts(p)
    P_succ = success_probability(p, n_budget)
    dec_label, dec_text = decision_from_probability(P_succ)

    print(">>> GEOMETRIA INTERNA (media sugli stati visitati)")
    print(f"  kappa_eff      : {kappa_eff:.3f}")
    print(f"  entropy_eff    : {entropy_eff:.3f}")
    print(f"  V0 (barriera)  : {V0:.4f}")
    print(f"  a_min (SAT)    : {A_MIN_SAT}")
    print()

    print(">>> TUNNELING LOVENTRE SU QUESTA ISTANZA")
    print(f"  p_tunnel(E)    : {p:.3e}")
    print(f"  E[N] (tentativi) : {expected_N:.3e}")
    print()

    print(">>> PROBABILITÀ DI SUCCESSO ENTRO N_budget")
    print(f"  P_success      : {P_succ:.3e}")
    print(f"  decision_label : {dec_label}")
    print(f"  decision_text  : {dec_text}")
    print()


def _parse_args() -> Tuple[str, float, int]:
    import sys

    name = "easy1"
    energy = 0.5
    n_budget = 10000

    if len(sys.argv) >= 2:
        name = sys.argv[1].strip()

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
    analyze_sat_instance(name, energy, n_budget, max_states=1000)


if __name__ == "__main__":
    main()
