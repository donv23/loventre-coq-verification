import math
import sys


# ----------------------------------------------------
# Famiglia critica SAT_crit_n – DNA Loventre interno
# ----------------------------------------------------

# Ordine delle istanze critiche (usato anche per a_min).
CRITICAL_SAT_LIST = [
    "sat_crit4",
    "sat_crit6",
    "sat_crit8",
    "sat_crit10",
    "sat_crit12",
    "sat_crit16",
]

# Firma interna: n_vars, num_clauses, kappa_eff, entropy_eff.
# κ_eff e H_eff crescono con n, simulando una geometria
# sempre più "curva" e concentrata.
CRITICAL_SAT_SIGNATURES = {
    "sat_crit4": {
        "n_vars": 4,
        "num_clauses": 5,
        "kappa_eff": 0.48,
        "entropy_eff": 0.62,
    },
    "sat_crit6": {
        "n_vars": 6,
        "num_clauses": 9,
        "kappa_eff": 0.57,
        "entropy_eff": 0.70,
    },
    "sat_crit8": {
        "n_vars": 8,
        "num_clauses": 13,
        "kappa_eff": 0.66,
        "entropy_eff": 0.78,
    },
    "sat_crit10": {
        "n_vars": 10,
        "num_clauses": 17,
        "kappa_eff": 0.75,
        "entropy_eff": 0.84,
    },
    "sat_crit12": {
        "n_vars": 12,
        "num_clauses": 21,
        "kappa_eff": 0.84,
        "entropy_eff": 0.89,
    },
    "sat_crit16": {
        "n_vars": 16,
        "num_clauses": 29,
        "kappa_eff": 0.93,
        "entropy_eff": 0.93,
    },
}

# Coefficienti del potenziale informazionale U = α·κ + β·H.
ALPHA = 1.1
BETA = 0.9


def barrier_height(kappa_eff: float, entropy_eff: float) -> float:
    """
    Altezza della barriera V0 derivata dal potenziale informazionale.

    U = α·κ + β·H, poi V0 = U^2 per amplificare la crescita con n.
    Una crescita quasi lineare di κ e H diventa crescita non lineare di V0.
    """
    U = ALPHA * kappa_eff + BETA * entropy_eff
    return U * U


def barrier_thickness(name: str) -> float:
    """
    Spessore minimo della barriera a_min in funzione dell'istanza critica.

    L'ordine in CRITICAL_SAT_LIST definisce un indice discreto;
    a_min cresce con l'indice e quindi con n_vars.
    """
    try:
        idx = CRITICAL_SAT_LIST.index(name)
    except ValueError:
        return 2.0
    # a_min parte da 1.8 e sale di 0.5 per ogni livello.
    return 1.8 + 0.5 * idx


def tunneling_probability(V0: float, a_min: float, energy: float) -> float:
    """
    Probabilità di tunneling per singolo tentativo.

        p_tunnel = exp( -2 * sqrt(max(V0 - E, 0)) * a_min )

    Se V0 <= E: regime sopra-barriera (p_tunnel = 1.0).
    """
    if V0 <= energy:
        return 1.0
    gap = V0 - energy
    if gap <= 0.0:
        return 1.0
    exponent = -2.0 * math.sqrt(gap) * a_min
    return math.exp(exponent)


def expected_attempts(p_tunnel: float) -> float:
    """
    Numero medio di tentativi E[N] ~ 1 / p_tunnel.
    """
    if p_tunnel <= 0.0:
        return float("inf")
    return 1.0 / p_tunnel


def success_probability(p_tunnel: float, n_budget: int) -> float:
    """
    Probabilità di almeno un successo entro n_budget tentativi.

        P_success = 1 - (1 - p_tunnel)^N_budget

    calcolata in modo stabile via log-spazio.
    """
    if p_tunnel <= 0.0:
        return 0.0
    if p_tunnel >= 1.0:
        return 1.0
    log_one_minus_p = math.log1p(-p_tunnel)
    inner = n_budget * log_one_minus_p
    return 1.0 - math.exp(inner)


def decision_label(p_success: float) -> str:
    """
    Etichetta qualitativa Loventre in base a P_success.
    """
    if p_success >= 0.95:
        return "Altamente raccomandato"
    if p_success >= 0.75:
        return "Raccomandato"
    if p_success >= 0.50:
        return "Marginale"
    if p_success >= 0.20:
        return "Molto rischioso"
    return "Quasi impossibile"


def run_critical_sat_family_scaling(energy: float, n_budget: int) -> None:
    """
    Scansione della famiglia SAT_crit_n nel senso Loventre.

    Per ogni istanza in CRITICAL_SAT_LIST:
      - legge n_vars, num_clauses, kappa_eff, entropy_eff,
      - calcola V0, a_min, p_tunnel(E), E[N], P_success,
      - produce una decisione qualitativa.
    """
    print()
    print("===================================================================")
    print("=== Loventre SAT Critical Family Scaling – Famiglia SAT_crit_n  ===")
    print("===================================================================")
    print(f"Energia E   : {energy}")
    print(f"N_budget    : {n_budget} tentativi meta per istanza")
    print(f"istanze_crit: {list(CRITICAL_SAT_LIST)}")
    print()
    print("name        n_vars  clauses  kappa_eff  entropy_eff   V0       a_min   p_tunnel(E)   E[N]          P_success   decision")
    print("------------------------------------------------------------------------------------------------------------------------")

    for name in CRITICAL_SAT_LIST:
        sig = CRITICAL_SAT_SIGNATURES[name]
        n_vars = sig["n_vars"]
        num_clauses = sig["num_clauses"]
        kappa_eff = sig["kappa_eff"]
        entropy_eff = sig["entropy_eff"]

        V0 = barrier_height(kappa_eff, entropy_eff)
        a_min = barrier_thickness(name)
        p_t = tunneling_probability(V0, a_min, energy)
        e_n = expected_attempts(p_t)
        p_s = success_probability(p_t, n_budget)
        label = decision_label(p_s)

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

    print()
    print("Nota (famiglia critica SAT_crit_n):")
    print("  - κ_eff, H_eff, V0 e lo spessore a_min crescono con n_vars,")
    print("    facendo esplodere E[N] e collassare P_success per N_budget polinomiale.")
    print("  - Fornisce una famiglia NP_like-critica Loventre da confrontare con SAT toy,")
    print("    che rimane P-like/precritica alle stesse risorse.")
    print()


def _parse_args():
    """
    Parsing semplice degli argomenti da linea di comando.

    Uso:
        python3 loventre_sat_critical_family_scaling.py [E] [N_budget]

    Default:
        E = 0.5
        N_budget = 1000
    """
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
    run_critical_sat_family_scaling(energy, n_budget)


if __name__ == "__main__":
    main()
