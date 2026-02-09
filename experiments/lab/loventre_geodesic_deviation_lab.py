"""
loventre_geodesic_deviation_lab.py

Lab Loventre–Einstein 2.2: geodesic deviation / caos Loventre.

1) Seed grid {1,2,3}x{1,2,3}:
   - confronta seed adiacenti (param/factor che differiscono di 1),
   - calcola un indice di "deviazione geodetica" tra le metriche aggregate,
   - individua regioni stabili vs caotiche.

2) Famiglia TSP_crit_n:
   - per n consecutivi in TSP_CRIT_N_LIST,
   - costruisce metriche effective (V0, a_min, p_tunnel, gamma_dilation, mass_eff, inert_idx),
   - calcola geodesic_deviation_index(n -> n_next).

3) Famiglia SAT_crit_n:
   - analogo a TSP, su SAT_CRIT_LIST.
"""

from typing import Dict, Tuple, List

from loventre_meta_engine import meta_analyze_seed, compute_geodesic_deviation_between_metrics
import loventre_seed_report as lsr

from loventre_instance_analysis import enrich_metrics_with_time_dilation

from loventre_tsp_critical_family_scaling import (
    CRITICAL_N_LIST as TSP_CRIT_N_LIST,
    CRITICAL_SIGNATURES as TSP_CRIT_SIGNATURES,
    barrier_height as tsp_crit_barrier_height,
    barrier_thickness as tsp_crit_barrier_thickness,
    tunneling_probability as tsp_crit_tunneling_probability,
)

from loventre_sat_critical_family_scaling import (
    CRITICAL_SAT_LIST as SAT_CRIT_LIST,
    CRITICAL_SAT_SIGNATURES as SAT_CRIT_SIGNATURES,
    barrier_height as sat_crit_barrier_height,
    barrier_thickness as sat_crit_barrier_thickness,
    tunneling_probability as sat_crit_tunneling_probability,
)


# ------------------------------------------------------------
# 1) Geodesic deviation sui seed della griglia toy
# ------------------------------------------------------------

SEEDS: List[Tuple[int, int]] = [
    (1, 1),
    (1, 2),
    (1, 3),
    (2, 1),
    (2, 2),
    (2, 3),
    (3, 1),
    (3, 2),
    (3, 3),
]


def _build_seed_metrics(energy: float) -> Dict[Tuple[int, int], Dict]:
    metrics_by_seed: Dict[Tuple[int, int], Dict] = {}
    for (param, factor) in SEEDS:
        m = meta_analyze_seed(param, factor, energy)
        metrics_by_seed[(param, factor)] = m
    return metrics_by_seed


def _neighbor_pairs() -> List[Tuple[Tuple[int, int], Tuple[int, int]]]:
    """
    Consideriamo come "vicini" i seed con distanza di Manhattan 1
    nella griglia {1,2,3}x{1,2,3}.
    """
    seed_set = set(SEEDS)
    pairs = []
    for (p, f) in SEEDS:
        for dp, df in [(1, 0), (0, 1)]:
            q = (p + dp, f + df)
            if q in seed_set:
                pairs.append(((p, f), q))
    return pairs


def print_seed_geodesic_deviation(energy: float) -> None:
    print("===================================================================")
    print("=== LOVENTRE GEODESIC DEVIATION – SEED GRID {1,2,3}x{1,2,3}     ===")
    print("===================================================================")
    print(f"Energia E   : {energy}")
    print()

    metrics_by_seed = _build_seed_metrics(energy)
    pairs = _neighbor_pairs()

    records = []
    for s1, s2 in pairs:
        m1 = metrics_by_seed[s1]
        m2 = metrics_by_seed[s2]
        dev = compute_geodesic_deviation_between_metrics(m1, m2)
        idx = dev["geodesic_deviation_index"]
        components = dev["components"]
        records.append({
            "seed1": s1,
            "seed2": s2,
            "index": idx,
            "components": components,
        })

    # Ordiniamo decrescente per caos (deviazione maggiore prima)
    records.sort(key=lambda r: r["index"], reverse=True)

    print("seed1 -> seed2    geod_dev   Δp_tunnel   Δgamma   ΔV0    Δmass    Δinertial")
    print("--------------------------------------------------------------------------------")
    for r in records:
        c = r["components"]
        def get_c(key):
            v = c.get(key)
            return f"{v:8.3f}" if isinstance(v, (int, float)) else "   ---- "
        print(
            f"{r['seed1']} -> {r['seed2']}   "
            f"{r['index']:8.3f}   "
            f"{get_c('p_tunnel')} "
            f"{get_c('gamma_dilation')} "
            f"{get_c('V0')} "
            f"{get_c('mass_mean')} "
            f"{get_c('inertial_difficulty_index')}"
        )
    print()


# ------------------------------------------------------------
# 2) Geodesic deviation sulla famiglia TSP_crit_n
# ------------------------------------------------------------

def _tsp_crit_metrics(n_cities: int, energy: float) -> Dict:
    """
    Costruisce una metrica effective Loventre per la famiglia TSP_crit_n
    al valore n_cities.
    """
    sig = TSP_CRIT_SIGNATURES[n_cities]
    kappa_eff = float(sig["kappa_eff"])
    entropy_eff = float(sig["entropy_eff"])

    V0 = float(tsp_crit_barrier_height(kappa_eff, entropy_eff))
    a_min = float(tsp_crit_barrier_thickness(n_cities))
    p_t = float(tsp_crit_tunneling_probability(V0, a_min, energy))

    # Time dilation + difficulty index (occupazione=1.0)
    m_time = enrich_metrics_with_time_dilation(
        {"p_tunnel": p_t, "barrier_occupancy": 1.0},
        gamma_cap=100.0,
        gamma_threshold_euclidean=2.0,
        gamma_threshold_hyperbolic=5.0,
    )
    gamma = float(m_time["gamma_dilation"])
    diff_idx = float(m_time["difficulty_index"])

    # Modello semplice di massa effettiva: m_eff ~ 1 + κ_eff + 0.5 H_eff
    mass_eff = 1.0 + kappa_eff + 0.5 * entropy_eff
    inert_idx = mass_eff * diff_idx

    return {
        "V0": V0,
        "a_min": a_min,
        "p_tunnel": p_t,
        "gamma_dilation": gamma,
        "difficulty_index": diff_idx,
        "mass_mean": mass_eff,
        "inertial_difficulty_index": inert_idx,
    }


def print_tsp_crit_geodesic_deviation(energy: float = 0.5) -> None:
    print("===================================================================")
    print("=== LOVENTRE GEODESIC DEVIATION – TSP_crit_n                    ===")
    print("===================================================================")
    print(f"Energia E   : {energy}")
    print(f"n_list_crit : {list(TSP_CRIT_N_LIST)}")
    print()

    n_list = list(TSP_CRIT_N_LIST)
    metrics_by_n: Dict[int, Dict] = {
        n: _tsp_crit_metrics(n, energy) for n in n_list
    }

    print("n1 -> n2    geod_dev   Δp_tunnel   Δgamma   ΔV0    Δmass    Δinertial")
    print("----------------------------------------------------------------------------")
    for n1, n2 in zip(n_list[:-1], n_list[1:]):
        m1 = metrics_by_n[n1]
        m2 = metrics_by_n[n2]
        dev = compute_geodesic_deviation_between_metrics(m1, m2)
        idx = dev["geodesic_deviation_index"]
        c = dev["components"]

        def get_c(key):
            v = c.get(key)
            return f"{v:8.3f}" if isinstance(v, (int, float)) else "   ---- "

        print(
            f"{n1:2d} -> {n2:2d}   "
            f"{idx:8.3f}   "
            f"{get_c('p_tunnel')} "
            f"{get_c('gamma_dilation')} "
            f"{get_c('V0')} "
            f"{get_c('mass_mean')} "
            f"{get_c('inertial_difficulty_index')}"
        )
    print()


# ------------------------------------------------------------
# 3) Geodesic deviation sulla famiglia SAT_crit_n
# ------------------------------------------------------------

def _sat_crit_metrics(name: str, energy: float) -> Dict:
    """
    Costruisce una metrica effective Loventre per la famiglia SAT_crit_n
    sull'istanza 'name'.
    """
    sig = SAT_CRIT_SIGNATURES[name]
    kappa_eff = float(sig["kappa_eff"])
    entropy_eff = float(sig["entropy_eff"])

    V0 = float(sat_crit_barrier_height(kappa_eff, entropy_eff))
    a_min = float(sat_crit_barrier_thickness(name))
    p_t = float(sat_crit_tunneling_probability(V0, a_min, energy))

    m_time = enrich_metrics_with_time_dilation(
        {"p_tunnel": p_t, "barrier_occupancy": 1.0},
        gamma_cap=100.0,
        gamma_threshold_euclidean=2.0,
        gamma_threshold_hyperbolic=5.0,
    )
    gamma = float(m_time["gamma_dilation"])
    diff_idx = float(m_time["difficulty_index"])

    mass_eff = 1.0 + kappa_eff + 0.5 * entropy_eff
    inert_idx = mass_eff * diff_idx

    return {
        "V0": V0,
        "a_min": a_min,
        "p_tunnel": p_t,
        "gamma_dilation": gamma,
        "difficulty_index": diff_idx,
        "mass_mean": mass_eff,
        "inertial_difficulty_index": inert_idx,
    }


def print_sat_crit_geodesic_deviation(energy: float = 0.5) -> None:
    print("===================================================================")
    print("=== LOVENTRE GEODESIC DEVIATION – SAT_crit_n                    ===")
    print("===================================================================")
    print(f"Energia E   : {energy}")
    print(f"istanze_crit: {list(SAT_CRIT_LIST)}")
    print()

    names = list(SAT_CRIT_LIST)
    metrics_by_name: Dict[str, Dict] = {
        name: _sat_crit_metrics(name, energy) for name in names
    }

    print("name1 -> name2    geod_dev   Δp_tunnel   Δgamma   ΔV0    Δmass    Δinertial")
    print("---------------------------------------------------------------------------------")
    for s1, s2 in zip(names[:-1], names[1:]):
        m1 = metrics_by_name[s1]
        m2 = metrics_by_name[s2]
        dev = compute_geodesic_deviation_between_metrics(m1, m2)
        idx = dev["geodesic_deviation_index"]
        c = dev["components"]

        def get_c(key):
            v = c.get(key)
            return f"{v:8.3f}" if isinstance(v, (int, float)) else "   ---- "

        print(
            f"{s1:10s} -> {s2:10s}   "
            f"{idx:8.3f}   "
            f"{get_c('p_tunnel')} "
            f"{get_c('gamma_dilation')} "
            f"{get_c('V0')} "
            f"{get_c('mass_mean')} "
            f"{get_c('inertial_difficulty_index')}"
        )
    print()


# ------------------------------------------------------------
# main
# ------------------------------------------------------------

def main() -> None:
    # 1) seed grid
    seed_energy = lsr.ENERGY_LEVEL
    print_seed_geodesic_deviation(seed_energy)

    # 2) family TSP_crit_n
    print_tsp_crit_geodesic_deviation(energy=0.5)

    # 3) family SAT_crit_n
    print_sat_crit_geodesic_deviation(energy=0.5)


if __name__ == "__main__":
    main()
