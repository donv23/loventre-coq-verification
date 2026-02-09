import math

# ============================================================
# 1. Potenziale informazionale U = alpha * kappa + beta * entropy
# ============================================================

def compute_potential(kappa, entropy, alpha=1.0, beta=1.0):
    """
    Calcola il potenziale informazionale U per uno stato.

    Parametri:
        kappa   : curvatura (float)
        entropy : entropia (float)
        alpha   : peso della curvatura
        beta    : peso dell'entropia

    Ritorna:
        U = alpha * kappa + beta * entropy
    """
    return alpha * kappa + beta * entropy


# ============================================================
# 2. Stima della soglia di barriera V0 da una lista di potenziali
#    (ad es. potenziali osservati durante una run)
# ============================================================

def estimate_V0(potentials, quantile=0.9):
    """
    Stima una soglia V0 come quantile della lista dei potenziali.

    Esempio: quantile=0.9 -> prende circa il 90° percentile come soglia di barriera.

    Parametri:
        potentials : lista di valori U (float)
        quantile   : valore tra 0 e 1

    Ritorna:
        V0 stimato (float)
    """
    if not potentials:
        raise ValueError("La lista dei potenziali è vuota, impossibile stimare V0.")

    sorted_p = sorted(potentials)
    idx = int((len(sorted_p) - 1) * quantile)
    return sorted_p[idx]


# ============================================================
# 3. Probabilità di tunneling p_tunnel(V0, a_min, E)
# ============================================================

def p_tunnel(V0, a_min, E):
    """
    Calcola la probabilità di tunneling creativo per un singolo tentativo.

    Formula:
        se E >= V0:
            p_tunnel = 1.0   (barriera superabile "classicamento")
        altrimenti:
            p_tunnel = exp( -2 * sqrt(V0 - E) * a_min )

    Parametri:
        V0    : potenziale di barriera (float)
        a_min : spessore effettivo minimo della barriera (numero di step/stati "duri") (float o int)
        E     : energia disponibile (float)

    Ritorna:
        p_tunnel in (0,1]
    """
    # Se l'energia è sufficiente o la barriera ha spessore nullo, attraversi "gratis"
    if E >= V0:
        return 1.0
    if a_min <= 0:
        return 1.0

    delta = V0 - E
    return math.exp(-2.0 * math.sqrt(delta) * a_min)


# ============================================================
# 4. Numero medio di tentativi prima di un lampo di invenzione
# ============================================================

def expected_attempts(p):
    """
    Numero medio di tentativi (N) prima del primo successo, con probabilità p.

    Se p è molto piccolo -> N è molto grande.
    Se p <= 0 -> ritorna infinito.
    """
    if p <= 0.0:
        return float('inf')
    return 1.0 / p


# ============================================================
# 5. Helper: calcola V0, p_tunnel ed E[N] da una lista di potenziali
# ============================================================

def tunneling_from_potentials(potentials, a_min, E, quantile=0.9):
    """
    Dato un elenco di potenziali U osservati durante una run,
    stima:

      - V0           : soglia di barriera (quantile)
      - p_tunnel     : probabilità di tunneling per tentativo
      - E[N]         : tentativi medi attesi

    Ritorna un dizionario con chiavi:
        'V0', 'p_tunnel', 'expected_attempts'
    """
    V0 = estimate_V0(potentials, quantile=quantile)
    p = p_tunnel(V0, a_min, E)
    N_mean = expected_attempts(p)

    return {
        "V0": V0,
        "p_tunnel": p,
        "expected_attempts": N_mean,
    }


# ============================================================
# 6. Esempio di utilizzo
# ============================================================

def example_usage():
    """
    Esempio semplice:
    - fissiamo una curvatura massima e un'entropia massima per un problema,
    - calcoliamo il potenziale V0,
    - fissiamo uno spessore di barriera a_min,
    - fissiamo un'energia E,
    - calcoliamo p_tunnel e il numero medio di tentativi.
    """

    # Dati di esempio (qui metti i valori che derivano dal tuo motore)
    kappa_max = 5.0     # curvatura massima osservata
    H_max = 3.0         # entropia massima osservata

    # Calcolo del potenziale di barriera
    V0 = compute_potential(kappa_max, H_max, alpha=1.0, beta=1.0)

    # Spessore minimo della barriera (in numero di step "duri")
    a_min = 4.0

    # Energia disponibile (quanto è "attrezzato" il sistema qui)
    E = 6.0

    # Calcolo della probabilità di tunneling
    p = p_tunnel(V0, a_min, E)

    # Numero medio di tentativi
    N_mean = expected_attempts(p)

    print("=== ESEMPIO TUNNELING CREATIVO ===")
    print("V0 (potenziale di barriera):", V0)
    print("a_min (spessore barriera):  ", a_min)
    print("Energia E:                  ", E)
    print("p_tunnel (per tentativo):   ", p)
    print("Tentativi medi attesi:      ", N_mean)


if __name__ == "__main__":
    example_usage()
