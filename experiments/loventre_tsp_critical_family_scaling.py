import math
import sys


# ---------------------------------------------
# Parametri di base per la famiglia TSP_crit_n
# ---------------------------------------------

# Lista delle taglie (numero di città) considerate.
CRITICAL_N_LIST = [8, 12, 16, 20, 24, 28]

# "DNA" Loventre per la famiglia critica: kappa_eff e entropy_eff
# sono scelti in modo da crescere con n, simulando una geometria
# sempre più "curva" e concentrata.
CRITICAL_SIGNATURES = {
    8:  {"kappa_eff": 0.45, "entropy_eff": 0.65},
    12: {"kappa_eff": 0.55, "entropy_eff": 0.75},
    16: {"kappa_eff": 0.65, "entropy_eff": 0.82},
    20: {"kappa_eff": 0.75, "entropy_eff": 0.88},
    24: {"kappa_eff": 0.85, "entropy_eff": 0.91},
    28: {"kappa_eff": 0.95, "entropy_eff": 0.93},
}

# Coefficienti del potenziale informazionale U = α·κ + β·H.
ALPHA = 1.2
BETA = 0.8


def barrier_height(kappa_eff: float, entropy_eff: float) -> float:
    '''Altezza della barriera V0 derivata dal potenziale informazionale.

    Si usa U = α·κ + β·H e poi V0 = U^2 per amplificare la crescita
    con n: una piccola crescita lineare di κ e H diventa una crescita
    non lineare di V0.
    '''
    U = ALPHA * kappa_eff + BETA * entropy_eff
    return U * U


def barrier_thickness(n_cities: int) -> float:
    '''Spessore minimo della barriera a_min in funzione di n.

    Si fa crescere a_min con n in modo discreto; questo, combinato con
    l'aumento di V0, rende la famiglia TSP_crit_n sempre più "NP_like-critica".
    '''
    index_by_n = {8: 0, 12: 1, 16: 2, 20: 3, 24: 4, 28: 5}
    idx = index_by_n.get(n_cities)
    if idx is None:
        # fallback prudente
        return 2.0
    # a_min parte da 2.0 e sale di 0.5 per ogni step.
    return 2.0 + 0.5 * idx


def tunneling_probability(V0: float, a_min: float, energy: float) -> float:
    '''Probabilità di tunneling per singolo tentativo.

    Formula Loventre (versione lampo):
        p_tunnel = exp( -2 * sqrt(max(V0 - E, 0)) * a_min )

    Se V0 <= E si entra in regime "sopra barriera": p_tunnel = 1.0.
    '''
    if V0 <= energy:
        return 1.0
    gap = V0 - energy
    if gap <= 0.0:
        return 1.0
    exponent = -2.0 * math.sqrt(gap) * a_min
    # Se exponent è molto negativo, exp(exponent) va a ~0.
    return math.exp(exponent)


def expected_attempts(p_tunnel: float) -> float:
    '''Numero medio di tentativi E[N] ~ 1 / p_tunnel.'''
    if p_tunnel <= 0.0:
        return float("inf")
    return 1.0 / p_tunnel


def success_probability(p_tunnel: float, n_budget: int) -> float:
    '''Probabilità di almeno un successo entro n_budget tentativi.

    P_success = 1 - (1 - p_tunnel)^N_budget, calcolata in modo stabile.
    '''
    if p_tunnel <= 0.0:
        return 0.0
    if p_tunnel >= 1.0:
        return 1.0
    # log(1 - p) < 0, quindi N * log(1 - p) è negativo.
    log_one_minus_p = math.log1p(-p_tunnel)
    inner = n_budget * log_one_minus_p
    # se inner è molto negativo, exp(inner) ~ 0 e P_success ~ 1
    return 1.0 - math.exp(inner)


def decision_label(p_success: float) -> str:
    '''Etichetta qualitativa Loventre in base a P_success.'''
    if p_success >= 0.95:
        return "Altamente raccomandato"
    if p_success >= 0.75:
        return "Raccomandato"
    if p_success >= 0.50:
        return "Marginale"
    if p_success >= 0.20:
        return "Molto rischioso"
    return "Quasi impossibile"


def run_critical_family_scaling(energy: float, n_budget: int) -> None:
    '''Scansione della famiglia TSP_crit_n nel senso Loventre.

    Per ogni n in CRITICAL_N_LIST:
      - legge kappa_eff, entropy_eff dalla tabella CRITICAL_SIGNATURES,
      - calcola V0, a_min, p_tunnel(E), E[N], P_success,
      - produce una decisione qualitativa.
    '''
    print()
    print("===================================================================")
    print("=== Loventre TSP Critical Family Scaling – Famiglia TSP_crit_n  ===")
    print("===================================================================")
    print(f"Energia E   : {energy}")
    print(f"N_budget    : {n_budget} tentativi meta per istanza")
    print(f"n_list_crit : {CRITICAL_N_LIST}")
    print()
    print("n_cities  kappa_eff  entropy_eff   V0       p_tunnel(E)   E[N]          P_success   decision")
    print("--------------------------------------------------------------------------------------------")

    for n_cities in CRITICAL_N_LIST:
        sig = CRITICAL_SIGNATURES[n_cities]
        kappa_eff = sig["kappa_eff"]
        entropy_eff = sig["entropy_eff"]

        V0 = barrier_height(kappa_eff, entropy_eff)
        a_min = barrier_thickness(n_cities)
        p_t = tunneling_probability(V0, a_min, energy)
        e_n = expected_attempts(p_t)
        p_s = success_probability(p_t, n_budget)
        label = decision_label(p_s)

        print(
            f"{n_cities:7d}  "
            f"{kappa_eff:8.3f}  "
            f"{entropy_eff:8.3f}  "
            f"{V0:6.4f}  "
            f"{p_t:11.3e}  "
            f"{e_n:11.3e}  "
            f"{p_s:9.3e} {label}"
        )

    print()
    print("Nota (famiglia critica TSP_crit_n):")
    print("  - Per energie fissate, V0 e a_min crescono con n,")
    print("    facendo crollare p_tunnel(E) e P_success per n grandi.")
    print("  - Questo realizza un comportamento 'NP_like-critico' nel senso Loventre,")
    print("    in contrasto con la famiglia TSP_n più regolare del laboratorio standard.")
    print()


def _parse_args():
    '''Parsing semplice degli argomenti da linea di comando.

    Uso:
        python3 loventre_tsp_critical_family_scaling.py [E] [N_budget]

    Default:
        E = 0.5
        N_budget = 1000
    '''
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
    run_critical_family_scaling(energy, n_budget)


if __name__ == "__main__":
    main()
