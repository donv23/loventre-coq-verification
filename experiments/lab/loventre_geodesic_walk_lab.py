import random

from loventre_instance_analysis import (
    geodesic_cost_for_state,
    choose_next_state_geodesic,
)


def generate_neighbors_around(state, num_neighbors=5, delta_C=0.5, delta_H=0.5):
    """
    Genera alcuni vicini toy attorno a uno stato dato, perturbando C e H.

    Parametri:
        state        : dict con chiavi 'C' e 'H'
        num_neighbors: quanti vicini generare
        delta_C      : ampiezza massima di perturbazione su C
        delta_H      : ampiezza massima di perturbazione su H

    Ritorna:
        lista di dict con chiavi 'C', 'H'
    """
    base_C = float(state.get("C", 0.0))
    base_H = float(state.get("H", 0.0))
    neighbors = []

    for _ in range(num_neighbors):
        dC = random.uniform(-delta_C, delta_C)
        dH = random.uniform(-delta_H, delta_H)
        new_C = max(0.0, base_C + dC)
        new_H = max(0.0, base_H + dH)
        neighbors.append({"C": new_C, "H": new_H})

    return neighbors


def geodesic_walk(
    start_state,
    steps=10,
    num_neighbors=5,
    alpha=1.0,
    beta=1.0,
    G_L=1.0,
    lambda_L=0.0,
    a_geod=1.0,
    b_geod=1.0,
    c_geod=0.0,
):
    """
    Esegue una "passeggiata geodetica" partendo da start_state:
      - a ogni step genera dei vicini,
      - sceglie il prossimo stato con choose_next_state_geodesic,
      - registra il cammino.

    Ritorna:
        path : lista di dict {"C", "H", "kappa", "U", "L"}
    """
    current = dict(start_state)
    path = []

    for t in range(steps):
        L_val, kappa_val, U_val = geodesic_cost_for_state(
            current,
            alpha=alpha,
            beta=beta,
            G_L=G_L,
            lambda_L=lambda_L,
            a_geod=a_geod,
            b_geod=b_geod,
            c_geod=c_geod,
        )
        path.append(
            {
                "step": t,
                "C": current["C"],
                "H": current["H"],
                "kappa": kappa_val,
                "U": U_val,
                "L": L_val,
            }
        )

        neighbors = generate_neighbors_around(current, num_neighbors=num_neighbors)
        result = choose_next_state_geodesic(
            current,
            neighbors,
            alpha=alpha,
            beta=beta,
            G_L=G_L,
            lambda_L=lambda_L,
            a_geod=a_geod,
            b_geod=b_geod,
            c_geod=c_geod,
        )
        current = result["next_state"]

    return path


def main():
    random.seed(42)

    start_state = {"C": 1.5, "H": 1.2}

    path = geodesic_walk(
        start_state,
        steps=12,
        num_neighbors=6,
        alpha=1.0,
        beta=1.0,
        G_L=1.0,
        lambda_L=0.0,
        a_geod=1.0,
        b_geod=1.0,
        c_geod=0.0,
    )

    print("=== Loventre Geodesic Walk Lab ===")
    print(f"Start state: C={start_state['C']:.3f}, H={start_state['H']:.3f}")
    print()
    print("step   C       H       kappa    U        L")
    print("-------------------------------------------------")
    for p in path:
        print(
            f"{p['step']:3d}  "
            f"{p['C']:7.3f}  "
            f"{p['H']:7.3f}  "
            f"{p['kappa']:7.3f}  "
            f"{p['U']:7.3f}  "
            f"{p['L']:7.3f}"
        )


if __name__ == "__main__":
    main()
