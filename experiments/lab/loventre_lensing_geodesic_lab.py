from __future__ import annotations

import math
import random
from typing import Any, Dict, List, Tuple

from loventre_instance_analysis import (
    compute_potential_from_kappa_entropy,
    compute_informational_mass,
)

State = Dict[str, Any]


# ============================================================
# LENSING INFORMAZIONALE: DEVIARE LE GEODETICHE
# ============================================================

def compute_lensing_potential(
    state: State,
    lenses: List[Dict[str, Any]] | None,
    default_pos: Tuple[float, float] = (0.0, 0.0),
    epsilon: float = 1e-6,
) -> float:
    """
    Calcola il termine di lensing Lens(s) per uno stato, dato un insieme di lenti.

    Ogni lente e' un dict con chiavi tipiche:
        - 'pos'  : posizione della lente (x, y)
        - 'mass' : massa della lente (float)
        - 'kind' : 'attractor' o 'repulsor'

    Definizione semplice:

        Lens(s) = somma_ℓ [ sign_ℓ * M_ℓ / (dist(pos(s), pos_ℓ) + epsilon) ]

    dove:
        sign_ℓ = -1 per attractor (abbassa il costo vicino alla lente)
        sign_ℓ = +1 per repulsor (alza il costo vicino alla lente)
    """
    if not lenses:
        return 0.0

    pos = state.get("pos", default_pos)
    if pos is None:
        pos = default_pos

    x_s = float(pos[0])
    y_s = float(pos[1])

    lens_term = 0.0

    for lens in lenses:
        center = lens.get("pos", default_pos)
        M = float(lens.get("mass", 1.0))
        kind = lens.get("kind", "attractor")

        x_l = float(center[0])
        y_l = float(center[1])

        dx = x_s - x_l
        dy = y_s - y_l
        dist = math.sqrt(dx * dx + dy * dy) + epsilon

        contrib = M / dist

        if kind == "repulsor":
            lens_term += contrib   # aumenta il costo vicino alla lente
        else:
            # attractor (default)
            lens_term -= contrib   # diminuisce il costo vicino alla lente

    return lens_term


# ============================================================
# GEODETICA CON MASSA + LENSING
# ============================================================

def geodesic_cost_for_state_with_mass_and_lensing(
    state: State,
    alpha: float = 1.0,
    beta: float = 1.0,
    G_L: float = 1.0,
    lambda_L: float = 0.0,
    a_geod: float = 1.0,
    b_geod: float = 1.0,
    c_geod: float = 0.0,
    m0: float = 1.0,
    w_C: float = 1.0,
    w_H: float = 0.5,
    inertia_weight: float = 1.0,
    lenses: List[Dict[str, Any]] | None = None,
    lens_weight: float = 1.0,
    default_pos: Tuple[float, float] = (0.0, 0.0),
) -> Tuple[float, float, float, float, float]:
    """
    Costo geodetico completo con:
        - massa informazionale m_L
        - curvatura kappa = G_L * m_L + lambda_L
        - potenziale U(s) = alpha * kappa + beta * H
        - base_cost = (a_geod * |kappa| + b_geod * H + c_geod) * (1 + inertia_weight * m_L)
        - lensing: L_total = base_cost + lens_weight * Lens(s)

    Parametri:
        state          : dict con almeno 'C', 'H', e opzionalmente 'pos' = (x, y)
        lenses         : lista di lenti (dict con 'pos', 'mass', 'kind')
        lens_weight    : quanto pesa il lensing rispetto al costo di base
        default_pos    : posizione di default se 'pos' manca

    Ritorna:
        (L_total, kappa, U, m_L, lens_term)
    """
    C_value = float(state.get("C", 0.0))
    H_value = float(state.get("H", 0.0))

    # Massa informazionale (principio di equivalenza)
    m_L = compute_informational_mass(
        C_value,
        H_value,
        m0=m0,
        w_C=w_C,
        w_H=w_H,
    )

    # Curvatura da massa
    kappa = G_L * m_L + lambda_L

    # Potenziale
    U_val = compute_potential_from_kappa_entropy(
        kappa,
        H_value,
        alpha=alpha,
        beta=beta,
    )

    # Costo base con inerzia
    base_cost = a_geod * abs(kappa) + b_geod * H_value + c_geod
    base_cost *= (1.0 + inertia_weight * m_L)

    # Lensing
    lens_term = 0.0
    if lenses is not None:
        lens_term = lens_weight * compute_lensing_potential(
            state,
            lenses,
            default_pos=default_pos,
        )

    L_total = base_cost + lens_term
    if L_total < 0.0:
        L_total = 0.0

    return L_total, kappa, U_val, m_L, lens_term


# ============================================================
# SCELTA DEL PROSSIMO STATO (GEODETICA LENSATA)
# ============================================================

def choose_next_state_geodesic_lensed(
    current_state: State,
    neighbors: List[State],
    alpha: float = 1.0,
    beta: float = 1.0,
    G_L: float = 1.0,
    lambda_L: float = 0.0,
    a_geod: float = 1.0,
    b_geod: float = 1.0,
    c_geod: float = 0.0,
    m0: float = 1.0,
    w_C: float = 1.0,
    w_H: float = 0.5,
    inertia_weight: float = 1.0,
    lenses: List[Dict[str, Any]] | None = None,
    lens_weight: float = 1.0,
    default_pos: Tuple[float, float] = (0.0, 0.0),
) -> Dict[str, Any]:
    """
    Sceglie il prossimo stato seguendo il principio geodetico
    deformato da massa + lensing.
    """
    if not neighbors:
        raise ValueError("La lista neighbors e' vuota: nessun prossimo stato disponibile.")

    best_index = 0
    best_state = neighbors[0]
    best_L, best_kappa, best_U, best_m_L, best_lens = geodesic_cost_for_state_with_mass_and_lensing(
        best_state,
        alpha=alpha,
        beta=beta,
        G_L=G_L,
        lambda_L=lambda_L,
        a_geod=a_geod,
        b_geod=b_geod,
        c_geod=c_geod,
        m0=m0,
        w_C=w_C,
        w_H=w_H,
        inertia_weight=inertia_weight,
        lenses=lenses,
        lens_weight=lens_weight,
        default_pos=default_pos,
    )

    all_costs = [best_L]
    all_kappa = [best_kappa]
    all_U = [best_U]
    all_m = [best_m_L]
    all_lens = [best_lens]

    for idx in range(1, len(neighbors)):
        s_candidate = neighbors[idx]
        L_val, kappa_val, U_val, m_L_val, lens_val = geodesic_cost_for_state_with_mass_and_lensing(
            s_candidate,
            alpha=alpha,
            beta=beta,
            G_L=G_L,
            lambda_L=lambda_L,
            a_geod=a_geod,
            b_geod=b_geod,
            c_geod=c_geod,
            m0=m0,
            w_C=w_C,
            w_H=w_H,
            inertia_weight=inertia_weight,
            lenses=lenses,
            lens_weight=lens_weight,
            default_pos=default_pos,
        )

        all_costs.append(L_val)
        all_kappa.append(kappa_val)
        all_U.append(U_val)
        all_m.append(m_L_val)
        all_lens.append(lens_val)

        if L_val < best_L:
            best_L = L_val
            best_kappa = kappa_val
            best_U = U_val
            best_m_L = m_L_val
            best_lens = lens_val
            best_state = s_candidate
            best_index = idx

    return {
        "next_state": best_state,
        "next_index": best_index,
        "L": best_L,
        "kappa": best_kappa,
        "U": best_U,
        "m_L": best_m_L,
        "lens_term": best_lens,
        "all_costs": all_costs,
        "all_kappa": all_kappa,
        "all_U": all_U,
        "all_m": all_m,
        "all_lens": all_lens,
    }


# ============================================================
# WALK LENSATO NELLO SPAZIO (C, H, pos)
# ============================================================

def _random_neighbor_with_pos(
    current_state: State,
    step_C: float = 0.3,
    step_H: float = 0.3,
    step_pos: float = 0.5,
) -> State:
    """
    Genera un vicino random partendo da current_state,
    modificando C, H e pos=(x,y).
    """
    C0 = float(current_state.get("C", 0.0))
    H0 = float(current_state.get("H", 0.0))
    pos0 = current_state.get("pos", (0.0, 0.0))

    x0 = float(pos0[0])
    y0 = float(pos0[1])

    C_new = max(0.0, C0 + random.uniform(-step_C, step_C))
    H_new = max(0.0, H0 + random.uniform(-step_H, step_H))

    x_new = x0 + random.uniform(-step_pos, step_pos)
    y_new = y0 + random.uniform(-step_pos, step_pos)

    return {"C": C_new, "H": H_new, "pos": (x_new, y_new)}


def geodesic_lensed_walk(
    start_state: State,
    steps: int,
    num_neighbors: int,
    lenses: List[Dict[str, Any]] | None = None,
    alpha: float = 1.0,
    beta: float = 1.0,
    G_L: float = 1.0,
    lambda_L: float = 0.0,
    a_geod: float = 1.0,
    b_geod: float = 1.0,
    c_geod: float = 0.0,
    m0: float = 1.0,
    w_C: float = 1.0,
    w_H: float = 0.5,
    inertia_weight: float = 1.0,
    lens_weight: float = 1.0,
) -> List[Dict[str, Any]]:
    """
    Esegue una geodesic walk deformata da massa + lensing.

    Ritorna una lista di dict con:
        step, C, H, pos_x, pos_y, kappa, U, m_L, L, lens_term
    """
    path: List[Dict[str, Any]] = []

    current: State = dict(start_state)

    for t in range(steps + 1):
        # Calcola costo sul punto corrente (per log)
        L_val, kappa_val, U_val, m_L_val, lens_val = geodesic_cost_for_state_with_mass_and_lensing(
            current,
            alpha=alpha,
            beta=beta,
            G_L=G_L,
            lambda_L=lambda_L,
            a_geod=a_geod,
            b_geod=b_geod,
            c_geod=c_geod,
            m0=m0,
            w_C=w_C,
            w_H=w_H,
            inertia_weight=inertia_weight,
            lenses=lenses,
            lens_weight=lens_weight,
        )

        pos = current.get("pos", (0.0, 0.0))
        x, y = float(pos[0]), float(pos[1])

        path.append(
            {
                "step": t,
                "C": current.get("C", 0.0),
                "H": current.get("H", 0.0),
                "pos_x": x,
                "pos_y": y,
                "kappa": kappa_val,
                "U": U_val,
                "m_L": m_L_val,
                "L": L_val,
                "lens_term": lens_val,
            }
        )

        # Genera neighbors e scegli il prossimo
        neighbors = [
            _random_neighbor_with_pos(current)
            for _ in range(num_neighbors)
        ]

        result = choose_next_state_geodesic_lensed(
            current,
            neighbors,
            alpha=alpha,
            beta=beta,
            G_L=G_L,
            lambda_L=lambda_L,
            a_geod=a_geod,
            b_geod=b_geod,
            c_geod=c_geod,
            m0=m0,
            w_C=w_C,
            w_H=w_H,
            inertia_weight=inertia_weight,
            lenses=lenses,
            lens_weight=lens_weight,
        )
        current = result["next_state"]

    return path


# ============================================================
# MAIN DI LABORATORIO
# ============================================================

def main() -> None:
    random.seed(123)

    # Definiamo qualche lente di prova:
    # - un attractor forte vicino all'origine
    # - un repulsor in alto a destra
    lenses = [
        {"pos": (0.0, 0.0), "mass": 3.0, "kind": "attractor"},
        {"pos": (2.0, 2.0), "mass": 2.0, "kind": "repulsor"},
    ]

    start_state: State = {"C": 1.5, "H": 1.0, "pos": (1.0, 0.5)}

    path = geodesic_lensed_walk(
        start_state,
        steps=12,
        num_neighbors=6,
        lenses=lenses,
        alpha=1.0,
        beta=1.0,
        G_L=1.0,
        lambda_L=0.0,
        a_geod=1.0,
        b_geod=1.0,
        c_geod=0.0,
        m0=1.0,
        w_C=1.0,
        w_H=0.5,
        inertia_weight=0.3,
        lens_weight=1.0,
    )

    print("=== Loventre Lensing Geodesic Walk Lab ===")
    print("Lenti attive:")
    for idx, ln in enumerate(lenses):
        print(
            f"  lens {idx}: pos={ln['pos']}, mass={ln['mass']}, kind={ln['kind']}"
        )
    print()
    print(
        "step   C       H       x_pos   y_pos   kappa    U        m_L      L        Lens"
    )
    print("---------------------------------------------------------------------------------")
    for p in path:
        print(
            f"{p['step']:3d}  "
            f"{p['C']:7.3f}  "
            f"{p['H']:7.3f}  "
            f"{p['pos_x']:7.3f}  "
            f"{p['pos_y']:7.3f}  "
            f"{p['kappa']:7.3f}  "
            f"{p['U']:7.3f}  "
            f"{p['m_L']:7.3f}  "
            f"{p['L']:7.3f}  "
            f"{p['lens_term']:7.3f}"
        )


if __name__ == "__main__":
    main()
