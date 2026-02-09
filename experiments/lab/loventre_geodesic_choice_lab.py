from loventre_instance_analysis import (
    geodesic_cost_for_state,
    choose_next_state_geodesic,
)


def main():
    # Stato corrente (puoi pensarlo come "configurazione attuale" del problema)
    current_state = {"C": 1.0, "H": 0.8}

    # Alcuni vicini toy: stati candidati come prossima mossa
    neighbors = [
        {"C": 0.8, "H": 0.9},   # un po' meno complesso, entropia alta
        {"C": 1.2, "H": 0.5},   # piu' complesso, entropia piu' bassa
        {"C": 0.6, "H": 0.4},   # piu' semplice e piu' ordinato
        {"C": 1.5, "H": 1.1},   # molto complesso e disordinato
    ]

    # Parametri di base Loventre
    alpha = 1.0
    beta = 1.0
    G_L = 1.0
    lambda_L = 0.0

    # Parametri geodetici (penalizza sia |kappa| che H)
    a_geod = 1.0
    b_geod = 1.0
    c_geod = 0.0

    result = choose_next_state_geodesic(
        current_state,
        neighbors,
        alpha=alpha,
        beta=beta,
        G_L=G_L,
        lambda_L=lambda_L,
        a_geod=a_geod,
        b_geod=b_geod,
        c_geod=c_geod,
    )

    print("=== Loventre Geodesic Choice Lab ===")
    print("Stato corrente: C={C}, H={H}".format(**current_state))
    print()
    print("Neighbors (C, H) e costi geodetici L:")

    for idx, (s, L_val, kappa_val, U_val) in enumerate(
        zip(
            neighbors,
            result["all_costs"],
            result["all_kappa"],
            result["all_U"],
        )
    ):
        print(
            f"  idx={idx:2d}  "
            f"C={s['C']:.3f}  H={s['H']:.3f}  "
            f"kappa={kappa_val:.3f}  U={U_val:.3f}  L={L_val:.3f}"
        )

    best = result["next_state"]
    print()
    print(f"Scelta geodetica: idx={result['next_index']}")
    print(
        "  next_state: C={C:.3f}, H={H:.3f}".format(
            C=best["C"],
            H=best["H"],
        )
    )
    print(
        f"  kappa={result['kappa']:.3f}, "
        f"U={result['U']:.3f}, "
        f"L={result['L']:.3f}"
    )


if __name__ == "__main__":
    main()
