"""
loventre_global_atlas_lab.py

Atlante globale Loventre – profilo macroscopico di:
  - seed grid {1,2,3} x {1,2,3},
  - famiglia TSP_crit_n,
  - famiglia SAT_crit_n.

Per ciascun blocco calcoliamo:
  - distribuzione di meta_label (se presente),
  - time_regime, energy_regime, mass_regime (se presenti),
  - presenza di horizon_detected / black_hole_risk (se presenti),
  - regime geodetico (geod_stable / geod_transition / geod_chaotic),
  - pattern P_like / precritical / critical / NP_like-black-hole per famiglie critiche.

L'obiettivo è avere una vista "Einstein-Loventre" globale:
  - spazio (barriere, V0),
  - tempo (gamma_dilation, time_regime),
  - massa (mass_mean, inertial_difficulty_index),
  - caos (geodesic deviation),
  - orizzonti / buchi neri informazionali.
"""

from typing import Dict, Tuple, List
from collections import Counter, defaultdict

from loventre_meta_engine import (
    meta_analyze_seed,
    compute_geodesic_deviation_between_metrics,
)
import loventre_seed_report as lsr

from loventre_instance_analysis import enrich_metrics_with_time_dilation

from loventre_tsp_critical_family_scaling import (
    CRITICAL_N_LIST as TSP_CRIT_N_LIST,
    CRITICAL_SIGNATURES as TSP_CRIT_SIGNATURES,
    barrier_height as tsp_crit_barrier_height,
    barrier_thickness as tsp_crit_barrier_thickness,
    tunneling_probability as tsp_crit_tunneling_probability,
    expected_attempts as tsp_crit_expected_attempts,
    success_probability as tsp_crit_success_probability,
    decision_label as tsp_crit_decision_label,
)

from loventre_sat_critical_family_scaling import (
    CRITICAL_SAT_LIST as SAT_CRIT_LIST,
    CRITICAL_SAT_SIGNATURES as SAT_CRIT_SIGNATURES,
    barrier_height as sat_crit_barrier_height,
    barrier_thickness as sat_crit_barrier_thickness,
    tunneling_probability as sat_crit_tunneling_probability,
    expected_attempts as sat_crit_expected_attempts,
    success_probability as sat_crit_success_probability,
    decision_label as sat_crit_decision_label,
)


# ============================================================
# Utility
# ============================================================


def _print_distribution(title: str, counter: Counter, total: int) -> None:
    print(f"{title}")
    if total == 0:
        print("  (nessun elemento)")
        return
    for key, count in counter.most_common():
        perc = 100.0 * count / total
        print(f"  - {str(key):25s}: {count:3d} ({perc:5.1f}%)")
    print()


def _bool_count(name: str, values: List[bool]) -> None:
    t = sum(1 for v in values if v)
    f = len(values) - t
    if not values:
        print(f"{name}: nessun dato.")
        return
    print(f"{name}:")
    print(f"  - True : {t:3d} ({100.0 * t / len(values):5.1f}%)")
    print(f"  - False: {f:3d} ({100.0 * f / len(values):5.1f}%)")
    print()


# ============================================================
# 1) Seed grid {1,2,3} x {1,2,3}
# ============================================================

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


def _neighbors_for_seed(p: int, f: int) -> List[Tuple[int, int]]:
    neigh = []
    seed_set = set(SEEDS)
    for dp, df in [(-1, 0), (1, 0), (0, -1), (0, 1)]:
        key = (p + dp, f + df)
        if key in seed_set:
            neigh.append(key)
    return neigh


def build_seed_grid_atlas(energy: float) -> None:
    print("===================================================================")
    print("=== LOVENTRE GLOBAL ATLAS – SEED GRID {1,2,3}x{1,2,3}          ===")
    print("===================================================================")
    print(f"Energia E   : {energy}")
    print()

    # 1) metriche di base via meta_analyze_seed
    metrics_by_seed: Dict[Tuple[int, int], Dict] = {}
    for (param, factor) in SEEDS:
        m = meta_analyze_seed(param, factor, energy)
        metrics_by_seed[(param, factor)] = m

    # 2) caos geodetico locale per ogni seed rispetto ai vicini
    atlas_records = []
    for (p, f) in SEEDS:
        m = metrics_by_seed[(p, f)]
        neighs = _neighbors_for_seed(p, f)

        devs = []
        for nk in neighs:
            m_nb = metrics_by_seed[nk]
            dev = compute_geodesic_deviation_between_metrics(m, m_nb)
            devs.append(dev["geodesic_deviation_index"])
        geod_chaos_index = max(devs) if devs else 0.0

        if geod_chaos_index < 0.1:
            geod_reg = "geod_stable"
        elif geod_chaos_index < 0.4:
            geod_reg = "geod_transition"
        else:
            geod_reg = "geod_chaotic"

        # meta_label e regimi, se meta_analyze_seed li ha messi dentro
        meta_label = m.get("meta_label", "unknown")
        time_regime = m.get("time_regime", "unknown")
        energy_regime = m.get("energy_regime", "unknown")
        mass_regime = m.get("mass_regime", "unknown")
        horizon = bool(m.get("horizon_detected", False))
        black_hole = bool(m.get("black_hole_risk", False))

        region = m.get("region", "unknown")
        difficulty_label = m.get("difficulty_label", "unknown")

        atlas_records.append(
            {
                "param": p,
                "factor": f,
                "region": region,
                "meta_label": meta_label,
                "time_regime": time_regime,
                "energy_regime": energy_regime,
                "mass_regime": mass_regime,
                "geod_chaos_index": geod_chaos_index,
                "geod_regime": geod_reg,
                "horizon_detected": horizon,
                "black_hole_risk": black_hole,
                "difficulty_label": difficulty_label,
            }
        )

    total = len(atlas_records)

    # 3) distribuzioni
    meta_counter = Counter(r["meta_label"] for r in atlas_records)
    time_counter = Counter(r["time_regime"] for r in atlas_records)
    energy_counter = Counter(r["energy_regime"] for r in atlas_records)
    mass_counter = Counter(r["mass_regime"] for r in atlas_records)
    geod_counter = Counter(r["geod_regime"] for r in atlas_records)
    region_counter = Counter(r["region"] for r in atlas_records)

    horizon_list = [r["horizon_detected"] for r in atlas_records]
    bh_list = [r["black_hole_risk"] for r in atlas_records]

    print("=== Distribuzione meta_label (seed grid) ===")
    _print_distribution("meta_label:", meta_counter, total)

    print("=== Distribuzione region (P_like / precritical / critical) ===")
    _print_distribution("region:", region_counter, total)

    print("=== Distribuzione time_regime (seed grid) ===")
    _print_distribution("time_regime:", time_counter, total)

    print("=== Distribuzione energy_regime (seed grid) ===")
    _print_distribution("energy_regime:", energy_counter, total)

    print("=== Distribuzione mass_regime (seed grid) ===")
    _print_distribution("mass_regime:", mass_counter, total)

    print("=== Distribuzione geod_regime (seed grid) ===")
    _print_distribution("geod_regime:", geod_counter, total)

    print("=== Orizzonti / buchi neri (seed grid) ===")
    _bool_count("horizon_detected", horizon_list)
    _bool_count("black_hole_risk", bh_list)

    # 4) elenco compatto di seed "notevoli"
    print("=== Seed notevoli (seed grid) ===")
    print("param factor  region      meta_label             geod_regime    geod_ch")
    print("----------------------------------------------------------------------------")
    # ordiniamo P_like / critical e caos alto / basso per leggibilità
    for r in sorted(
        atlas_records,
        key=lambda x: (x["region"], -x["geod_chaos_index"]),
    ):
        print(
            f"{r['param']:5d} {r['factor']:6d} "
            f"{r['region']:9s} "
            f"{str(r['meta_label'])[:22]:22s} "
            f"{r['geod_regime']:12s} "
            f"{r['geod_chaos_index']:7.3f}"
        )
    print()


# ============================================================
# 2) Famiglia TSP_crit_n
# ============================================================


def _tsp_crit_metrics(n_cities: int, energy: float, n_budget: int) -> Dict:
    sig = TSP_CRIT_SIGNATURES[n_cities]
    kappa_eff = float(sig["kappa_eff"])
    entropy_eff = float(sig["entropy_eff"])

    V0 = float(tsp_crit_barrier_height(kappa_eff, entropy_eff))
    a_min = float(tsp_crit_barrier_thickness(n_cities))
    p_t = float(tsp_crit_tunneling_probability(V0, a_min, energy))
    e_n = float(tsp_crit_expected_attempts(p_t))
    p_s = float(tsp_crit_success_probability(p_t, n_budget))
    dec = tsp_crit_decision_label(p_s)

    m_time = enrich_metrics_with_time_dilation(
        {"p_tunnel": p_t, "barrier_occupancy": 1.0},
        gamma_cap=100.0,
        gamma_threshold_euclidean=2.0,
        gamma_threshold_hyperbolic=5.0,
    )
    gamma = float(m_time["gamma_dilation"])
    time_reg = str(m_time["time_regime"])

    # Modello semplice di massa effettiva coerente con altri lab
    mass_eff = 1.0 + kappa_eff + 0.5 * entropy_eff
    inert_idx = mass_eff * float(m_time["difficulty_index"])

    # Classificazione Loventre grossolana per la famiglia critica:
    #   - P_like_like       : p_tunnel >= 1e-2 e gamma <= 5
    #   - NP_like_critico   : altro
    #   - NP_like_black_hole: p_tunnel < 1e-6 e gamma >= 10
    if p_t >= 1e-2 and gamma <= 5.0:
        meta_label = "P_like_like"
    else:
        meta_label = "NP_like_critico"
    if p_t < 1e-6 and gamma >= 10.0:
        meta_label = "NP_like_black_hole"

    return {
        "n_cities": n_cities,
        "kappa_eff": kappa_eff,
        "entropy_eff": entropy_eff,
        "V0": V0,
        "a_min": a_min,
        "p_tunnel": p_t,
        "E_N": e_n,
        "P_success": p_s,
        "decision": dec,
        "gamma_dilation": gamma,
        "time_regime": time_reg,
        "mass_eff": mass_eff,
        "inertial_difficulty_index": inert_idx,
        "meta_label": meta_label,
    }


def build_tsp_crit_atlas(energy: float = 0.5, n_budget: int = 1000) -> None:
    print("===================================================================")
    print("=== LOVENTRE GLOBAL ATLAS – TSP_crit_n (famiglia critica TSP)   ===")
    print("===================================================================")
    print(f"Energia E   : {energy}")
    print(f"N_budget    : {n_budget} tentativi meta per istanza")
    print(f"n_list_crit : {list(TSP_CRIT_N_LIST)}")
    print()

    records: List[Dict] = []
    for n in TSP_CRIT_N_LIST:
        records.append(_tsp_crit_metrics(n, energy, n_budget))

    total = len(records)

    meta_counter = Counter(r["meta_label"] for r in records)
    time_counter = Counter(r["time_regime"] for r in records)

    # massa_eff in tre fasce grossolane
    mass_reg_counter = Counter()
    for r in records:
        m = r["mass_eff"]
        if m < 2.0:
            mass_reg_counter["mass_light"] += 1
        elif m < 2.3:
            mass_reg_counter["mass_medium"] += 1
        else:
            mass_reg_counter["mass_heavy"] += 1

    print("=== Distribuzione meta_label (TSP_crit_n) ===")
    _print_distribution("meta_label:", meta_counter, total)

    print("=== Distribuzione time_regime (TSP_crit_n) ===")
    _print_distribution("time_regime:", time_counter, total)

    print("=== Distribuzione mass_regime (TSP_crit_n) ===")
    _print_distribution("mass_regime (eff):", mass_reg_counter, total)

    print("=== Dettaglio istanze TSP_crit_n ===")
    print("n_cities  meta_label             time_regime        V0      p_tunnel     gamma   mass_eff  decision")
    print("--------------------------------------------------------------------------------------------------")
    for r in records:
        print(
            f"{r['n_cities']:8d}  "
            f"{r['meta_label']:22s} "
            f"{r['time_regime']:16s} "
            f"{r['V0']:7.4f}  "
            f"{r['p_tunnel']:10.3e} "
            f"{r['gamma_dilation']:6.2f}  "
            f"{r['mass_eff']:8.3f}  "
            f"{r['decision']}"
        )
    print()


# ============================================================
# 3) Famiglia SAT_crit_n
# ============================================================


def _sat_crit_metrics(name: str, energy: float, n_budget: int) -> Dict:
    sig = SAT_CRIT_SIGNATURES[name]
    kappa_eff = float(sig["kappa_eff"])
    entropy_eff = float(sig["entropy_eff"])

    V0 = float(sat_crit_barrier_height(kappa_eff, entropy_eff))
    a_min = float(sat_crit_barrier_thickness(name))
    p_t = float(sat_crit_tunneling_probability(V0, a_min, energy))
    e_n = float(sat_crit_expected_attempts(p_t))
    p_s = float(sat_crit_success_probability(p_t, n_budget))
    dec = sat_crit_decision_label(p_s)

    m_time = enrich_metrics_with_time_dilation(
        {"p_tunnel": p_t, "barrier_occupancy": 1.0},
        gamma_cap=100.0,
        gamma_threshold_euclidean=2.0,
        gamma_threshold_hyperbolic=5.0,
    )
    gamma = float(m_time["gamma_dilation"])
    time_reg = str(m_time["time_regime"])

    mass_eff = 1.0 + kappa_eff + 0.5 * entropy_eff
    inert_idx = mass_eff * float(m_time["difficulty_index"])

    if p_t >= 1e-2 and gamma <= 5.0:
        meta_label = "P_like_like"
    else:
        meta_label = "NP_like_critico"
    if p_t < 1e-6 and gamma >= 10.0:
        meta_label = "NP_like_black_hole"

    return {
        "name": name,
        "n_vars": int(sig["n_vars"]),
        "num_clauses": int(sig["num_clauses"]),
        "kappa_eff": kappa_eff,
        "entropy_eff": entropy_eff,
        "V0": V0,
        "a_min": a_min,
        "p_tunnel": p_t,
        "E_N": e_n,
        "P_success": p_s,
        "decision": dec,
        "gamma_dilation": gamma,
        "time_regime": time_reg,
        "mass_eff": mass_eff,
        "inertial_difficulty_index": inert_idx,
        "meta_label": meta_label,
    }


def build_sat_crit_atlas(energy: float = 0.5, n_budget: int = 1000) -> None:
    print("===================================================================")
    print("=== LOVENTRE GLOBAL ATLAS – SAT_crit_n (famiglia critica SAT)   ===")
    print("===================================================================")
    print(f"Energia E   : {energy}")
    print(f"N_budget    : {n_budget} tentativi meta per istanza")
    print(f"istanze_crit: {list(SAT_CRIT_LIST)}")
    print()

    records: List[Dict] = []
    for name in SAT_CRIT_LIST:
        records.append(_sat_crit_metrics(name, energy, n_budget))

    total = len(records)

    meta_counter = Counter(r["meta_label"] for r in records)
    time_counter = Counter(r["time_regime"] for r in records)

    mass_reg_counter = Counter()
    for r in records:
        m = r["mass_eff"]
        if m < 2.0:
            mass_reg_counter["mass_light"] += 1
        elif m < 2.3:
            mass_reg_counter["mass_medium"] += 1
        else:
            mass_reg_counter["mass_heavy"] += 1

    print("=== Distribuzione meta_label (SAT_crit_n) ===")
    _print_distribution("meta_label:", meta_counter, total)

    print("=== Distribuzione time_regime (SAT_crit_n) ===")
    _print_distribution("time_regime:", time_counter, total)

    print("=== Distribuzione mass_regime (SAT_crit_n) ===")
    _print_distribution("mass_regime (eff):", mass_reg_counter, total)

    print("=== Dettaglio istanze SAT_crit_n ===")
    print("name        meta_label             time_regime        V0      p_tunnel     gamma   mass_eff  decision")
    print("------------------------------------------------------------------------------------------------------")
    for r in records:
        print(
            f"{r['name']:10s}  "
            f"{r['meta_label']:22s} "
            f"{r['time_regime']:16s} "
            f"{r['V0']:7.4f}  "
            f"{r['p_tunnel']:10.3e} "
            f"{r['gamma_dilation']:6.2f}  "
            f"{r['mass_eff']:8.3f}  "
            f"{r['decision']}"
        )
    print()


# ============================================================
# main
# ============================================================


def main() -> None:
    energy_seed = lsr.ENERGY_LEVEL
    n_budget_default = 10000

    build_seed_grid_atlas(energy_seed)
    build_tsp_crit_atlas(energy=0.5, n_budget=1000)
    build_sat_crit_atlas(energy=0.5, n_budget=1000)


if __name__ == "__main__":
    main()
