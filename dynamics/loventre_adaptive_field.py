"""
loventre_adaptive_field.py

Modulo Loventre Adaptive Field (LAF):
Costruisce un meta–aggregatore dinamico che combina:
  - strategy_score locale del seed,
  - rischio medio (risk_index) dei vicini,
  - caos geodetico medio dei vicini,
per generare una policy di esplorazione adattiva.

Interpretazione fisico–informazionale:
  - risk_index alto → campo di curvatura instabile (barriera),
  - chaos_mean alto → geodetica turbolenta,
  - strategy_score alto → località efficiente.
La combinazione produce un potenziale informazionale Loventre che guida
la direzione ottimale di esplorazione (INSISTI / ESPLORA / RITIRA).
"""

import math
from typing import Dict, Any, Tuple, List
from collections import defaultdict, Counter

from loventre_meta_engine import meta_analyze_seed

# === Parametri globali ===
SEEDS = [(i, j) for i in [1, 2, 3] for j in [1, 2, 3]]

W_RISK = 0.5
W_STRATEGY = 0.3
W_CHAOS = 0.2

def _neighbors(p: int, f: int) -> List[Tuple[int, int]]:
    neigh = []
    for dp, df in [(-1,0),(1,0),(0,-1),(0,1)]:
        if (p+dp, f+df) in SEEDS:
            neigh.append((p+dp,f+df))
    return neigh

def _compute_LAF_potential(strategy_score: float, risk_mean: float, chaos_mean: float) -> float:
    s_term = W_STRATEGY * max(0.0, min(1.0, strategy_score))
    r_term = W_RISK * (1.0 - min(1.0, risk_mean / 10.0))
    c_term = W_CHAOS * (1.0 - min(1.0, chaos_mean))
    return s_term + r_term + c_term

def _policy_from_potential(phi: float) -> str:
    if phi >= 0.75:
        return "INSISTI"
    if phi >= 0.45:
        return "ESPLORA"
    return "RITIRA"

def build_loventre_adaptive_field(energy: float = 1.5, n_budget: int = 10000) -> None:
    from loventre_meta_portfolio_lab import build_seed_metrics_map

    # Otteniamo metriche locali (strategy_score, risk_index, geod_chaos_index)
    data_map = build_seed_metrics_map(energy, n_budget)

    print("===================================================================")
    print("=== LOVENTRE ADAPTIVE FIELD (Einstein–Loventre)                 ===")
    print("===================================================================")
    print(f"Energia E   : {energy}")
    print(f"N_budget    : {n_budget}")
    print()
    print("param factor  strat_score  risk_mean  chaos_mean  LAF_potential  policy")
    print("-----------------------------------------------------------------------")

    results = []
    for (p,f), m in data_map.items():
        neigh = _neighbors(p,f)
        risks = [data_map[n]["risk_index"] for n in neigh if "risk_index" in data_map[n]]
        chaos = [data_map[n]["geod_chaos_index"] for n in neigh if "geod_chaos_index" in data_map[n]]

        risk_mean = sum(risks)/len(risks) if risks else 0.0
        chaos_mean = sum(chaos)/len(chaos) if chaos else 0.0

        phi = _compute_LAF_potential(m.get("strategy_score",0.0), risk_mean, chaos_mean)
        policy = _policy_from_potential(phi)

        results.append({
            "param": p, "factor": f,
            "strategy_score": m.get("strategy_score",0.0),
            "risk_mean": risk_mean,
            "chaos_mean": chaos_mean,
            "LAF_potential": phi,
            "policy": policy,
        })

        print(f"{p:5d} {f:6d} "
              f"{m.get('strategy_score',0.0):11.3f} "
              f"{risk_mean:9.3f} {chaos_mean:10.3f} "
              f"{phi:13.3f} {policy:>10s}")

    print()
    counter = Counter(r["policy"] for r in results)
    print("Distribuzione delle policy:")
    for k,v in counter.items():
        print(f"  {k:10s}: {v} ({100*v/len(results):.1f}%)")
    print()
    # Agenda di esplorazione ordinata per policy + LAF_potential
    priority = {"INSISTI": 0, "ESPLORA": 1, "RITIRA": 2}

    ranked = sorted(
        results,
        key=lambda r: (priority.get(r["policy"], 3), -r["LAF_potential"])
    )

    print("Agenda di esplorazione (priorità Loventre):")
    print("param factor  policy      LAF_potential  risk_mean  chaos_mean")
    print("----------------------------------------------------------------")
    for r in ranked:
        print(
            f"{r['param']:5d} {r['factor']:6d} "
            f"{r['policy']:10s} "
            f"{r['LAF_potential']:13.3f} "
            f"{r['risk_mean']:9.3f} "
            f"{r['chaos_mean']:10.3f}"
        )
    print()

# ================================================================
# === LOVENTRE ADAPTIVE FIELD – MULTIFAMIGLIA (P vs NP_like)   ===
# ================================================================
def build_multifamily_field():
    from collections import Counter
    print()
    print("="*67)
    print("=== LOVENTRE ADAPTIVE FIELD – MULTIFAMIGLIA (P vs NP_like)     ===")
    print("="*67)

    # Valori riassuntivi per ciascuna famiglia:
    # - risk_mean: rischio Einstein–Loventre medio (0–10),
    # - mass_eff : massa informazionale effettiva media,
    # - time_hyp : frazione di istanze in regime time_hyperbolic (0–1).
    families = [
        ("seed_grid",   {"risk_mean": 1.52, "mass_eff": 2.05, "time_hyp": 0.222}),
        ("TSP_crit_n",  {"risk_mean": 6.11, "mass_eff": 2.40, "time_hyp": 0.833}),
        ("SAT_crit_n",  {"risk_mean": 5.98, "mass_eff": 2.30, "time_hyp": 0.833}),
    ]

    results = []
    for name, data in families:
        r_mean = data["risk_mean"]
        m_mean = data["mass_eff"]
        t_hyp  = data["time_hyp"]

        # Potenziale Loventre globale (già usato prima):
        #   - più è alto → più la famiglia è "investibile".
        alpha, beta, gamma = 0.6, 0.3, 0.4
        potential = alpha * (1.0 - r_mean / 10.0)                   + beta  * (1.0 - t_hyp)                   + gamma * (1.0 - m_mean / 3.0)

        # Curvatura informazionale globale K_globale ∈ [0,1]:
        #   - contribuiscono:
        #       * rischio medio (r_mean / 10),
        #       * quota di tempo iperbolico (t_hyp),
        #       * massa effettiva normalizzata (m_mean / 3).
        #   - 0   ≈ quasi euclideo (P-like),
        #   - 1   ≈ fortemente "negativo" / NP_like-critico (quasi buco nero).
        raw_K = (
            0.5 * (r_mean / 10.0) +   # peso forte al rischio
            0.3 * t_hyp +             # peso alla quota time_hyperbolic
            0.2 * (m_mean / 3.0)      # massa effettiva normalizzata
        )
        K_globale = max(0.0, min(1.0, raw_K))

        if potential > 0.7:
            policy = "INSISTI"
        elif potential > 0.5:
            policy = "ESPLORA"
        else:
            policy = "RITIRA"

        results.append({
            "famiglia": name,
            "risk_mean": r_mean,
            "mass_eff": m_mean,
            "time_hyp": t_hyp,
            "potential_global": potential,
            "K_globale": K_globale,
            "policy": policy,
        })

    print()
    print("famiglia     risk_mean  mass_eff  time_hyperbolic%  K_globale  potential_global  policy")
    print("-----------------------------------------------------------------------------------------")
    for r in results:
        print(
            f"{r['famiglia']:12s} "
            f"{r['risk_mean']:10.2f} "
            f"{r['mass_eff']:9.2f} "
            f"{r['time_hyp']*100:12.1f}% "
            f"{r['K_globale']:10.2f} "
            f"{r['potential_global']:16.2f} "
            f"{r['policy']:10s}"
        )
    print()

    c = Counter(r["policy"] for r in results)
    print("Distribuzione policy (macro–famiglie):")
    for k, v in c.items():
        print(f"  {k:8s}: {v}")
    print()

    print("Interpretazione K_globale:")
    print("  - ≈0.0: curvatura quasi-euclidea / regime P-like accessibile.")
    print("  - ≈1.0: curvatura fortemente negativa (NP_like-critico / quasi buco nero Loventre).")
    print()
# auto-run multifamily
build_multifamily_field()


# === Mini–bridge di supporto ===
def main():
    import sys
    energy = 1.5
    n_budget = 10000
    if len(sys.argv) > 1:
        try: energy = float(sys.argv[1])
        except: pass
    if len(sys.argv) > 2:
        try: n_budget = int(sys.argv[2])
        except: pass
    build_loventre_adaptive_field(energy, n_budget)

if __name__ == "__main__":
    main()
