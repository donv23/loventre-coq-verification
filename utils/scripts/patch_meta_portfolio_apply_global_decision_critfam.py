from pathlib import Path
import re

MARKER = "# === LOVENTRE_PATCH_APPLY_GLOBAL_DECISION_CRITFAM ==="


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    target = root / "loventre_meta_portfolio_lab.py"

    if not target.exists():
        print(f"[Loventre] ERRORE: file non trovato: {target}")
        return

    src = target.read_text(encoding="utf-8")

    # Idempotenza: se abbiamo già patchato, usciamo.
    if MARKER in src:
        print(
            "[Loventre] print_tsp_critical_portfolio/print_sat_critical_portfolio "
            "già aggiornate con global_decision per famiglie critiche (marker trovato). "
            "Nessuna modifica necessaria."
        )
        return

    # Ritagliamo le vecchie definizioni delle due funzioni (blocchi grossi)
    pattern_tsp = re.compile(
        r"def print_tsp_critical_portfolio\([^)]*\):[\s\S]*?Nota meta-portafoglio TSP_crit_n:[\s\S]*?print\(\)\n",
        re.MULTILINE,
    )

    pattern_sat = re.compile(
        r"def print_sat_critical_portfolio\([^)]*\):[\s\S]*?Nota meta-portafoglio SAT_crit_n:[\s\S]*?print\(\)\n",
        re.MULTILINE,
    )

    # Nuova versione: costruisce record → passa al helper → stampa con G_dec/G_col/G_scr

    block_tsp = '''def print_tsp_critical_portfolio(energy: float = 0.5, n_budget: int = 1000) -> None:
    """
    Stampa un meta-portafoglio Loventre per la famiglia TSP_crit_n.
    """
    # === LOVENTRE_PATCH_APPLY_GLOBAL_DECISION_CRITFAM ===
    from loventre_instance_analysis import enrich_metrics_with_time_dilation

    print()
    print("===================================================================")
    print("=== LOVENTRE META-PORTFOLIO – TSP_crit_n (famiglia critica TSP) ===")
    print("===================================================================")
    print(f"Energia E   : {energy}")
    print(f"N_budget    : {n_budget} tentativi meta per istanza")
    print(f"n_list_crit : {list(TSP_CRIT_N_LIST)}")
    print()
    print(
        "n_cities  kappa_eff  entropy_eff   V0       a_min   p_tunnel(E)   E[N]          P_success   "
        "gamma_dil  mass_eff  inert_idx   time_regime        decision              G_dec  G_col  G_scr"
    )
    print("-----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------")

    records = []

    for n_cities in TSP_CRIT_N_LIST:
        sig = TSP_CRIT_SIGNATURES[n_cities]
        kappa_eff = sig["kappa_eff"]
        entropy_eff = sig["entropy_eff"]
        V0 = tsp_crit_barrier_height(kappa_eff, entropy_eff)
        a_min = tsp_crit_barrier_thickness(n_cities)
        p_t = tsp_crit_tunneling_probability(V0, a_min, energy)
        e_n = tsp_crit_expected_attempts(p_t)
        p_s = tsp_crit_success_probability(p_t, n_budget)
        label = tsp_crit_decision_label(p_s)

        metrics_dil = enrich_metrics_with_time_dilation(
            {"p_tunnel": p_t, "barrier_occupancy": 1.0},
            gamma_cap=100.0,
            gamma_threshold_euclidean=2.0,
            gamma_threshold_hyperbolic=5.0,
        )
        gamma_dil = metrics_dil["gamma_dilation"]
        time_regime = metrics_dil["time_regime"]

        mass_eff, inertial_idx = _effective_mass_and_inertia(
            kappa_eff,
            entropy_eff,
            gamma_dil,
            barrier_occupancy=1.0,
            m0=1.0,
            w_kappa=1.0,
            w_H=0.5,
        )

        rec = {
            "family": "TSP_crit_n",
            "n_cities": n_cities,
            "kappa_eff": kappa_eff,
            "entropy_eff": entropy_eff,
            "V0": V0,
            "a_min": a_min,
            "p_tunnel": p_t,
            "E_N": e_n,
            "P_success": p_s,
            "gamma_dilation": gamma_dil,
            "time_regime": time_regime,
            "mass_eff": mass_eff,
            "inertial_idx": inertial_idx,
            "decision_label": label,
        }
        records.append(rec)

    try:
        enriched = loventre_attach_global_decision_to_family(
            records, family_name="TSP_crit_n"
        )
    except Exception:
        enriched = records

    for r in enriched:
        gd = r.get("loventre_global") or {}
        g_dec = gd.get("global_decision", "N/A") or "N/A"
        g_col = gd.get("global_color", "N/A") or "N/A"
        g_scr = gd.get("global_score", 0.0) or 0.0

        print(
            f"{r['n_cities']:7d}  "
            f"{r['kappa_eff']:8.3f}  "
            f"{r['entropy_eff']:8.3f}  "
            f"{r['V0']:6.4f}  "
            f"{r['a_min']:6.2f}  "
            f"{r['p_tunnel']:11.3e}  "
            f"{r['E_N']:11.3e}  "
            f"{r['P_success']:9.3e}  "
            f"{r['gamma_dilation']:10.2f}  "
            f"{r['mass_eff']:8.3f}  "
            f"{r['inertial_idx']:11.3f}  "
            f"{r['time_regime']:13s}  "
            f"{r['decision_label']:20s}  "
            f"{g_dec:6s}  "
            f"{g_col:5s}  "
            f"{g_scr:6.3f}"
        )

    print()
    print("Nota meta-portafoglio TSP_crit_n:")
    print("  - V0 e lo spessore a_min crescono con n,")
    print("    facendo esplodere E[N] e collassare P_success con N_budget polinomiale.")
    print("  - La massa informazionale effettiva e l'indice inerziale crescono anch'essi,")
    print("    rendendo la dinamica progressivamente più pesante e time_hyperbolic.")
    print("  - Questo fornisce un esempio esplicito di famiglia NP_like-critica Loventre,")
    print("    da confrontare con SAT toy e TSP toy che rimangono P-like/precritici.")
    print()
'''

    block_sat = '''def print_sat_critical_portfolio(energy: float = 0.5, n_budget: int = 1000) -> None:
    """
    Meta-portafoglio Loventre per la famiglia SAT_crit_n.
    """
    from loventre_instance_analysis import enrich_metrics_with_time_dilation

    print()
    print("===================================================================")
    print("=== LOVENTRE META-PORTFOLIO – SAT_crit_n (famiglia critica SAT) ===")
    print("===================================================================")
    print(f"Energia E   : {energy}")
    print(f"N_budget    : {n_budget} tentativi meta per istanza")
    print(f"istanze_crit: {list(SAT_CRIT_LIST)}")
    print()
    print(
        "name        n_vars  clauses  kappa_eff  entropy_eff   V0       a_min   p_tunnel(E)   "
        "E[N]          P_success   gamma_dil  mass_eff  inert_idx   time_regime        decision              G_dec  G_col  G_scr"
    )
    print("--------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------")

    records = []

    for name in SAT_CRIT_LIST:
        sig = SAT_CRIT_SIGNATURES[name]
        n_vars = sig["n_vars"]
        num_clauses = sig["num_clauses"]
        kappa_eff = sig["kappa_eff"]
        entropy_eff = sig["entropy_eff"]

        V0 = sat_crit_barrier_height(kappa_eff, entropy_eff)
        a_min = sat_crit_barrier_thickness(name)
        p_t = sat_crit_tunneling_probability(V0, a_min, energy)
        e_n = sat_crit_expected_attempts(p_t)
        p_s = sat_crit_success_probability(p_t, n_budget)
        label = sat_crit_decision_label(p_s)

        metrics_dil = enrich_metrics_with_time_dilation(
            {"p_tunnel": p_t, "barrier_occupancy": 1.0},
            gamma_cap=100.0,
            gamma_threshold_euclidean=2.0,
            gamma_threshold_hyperbolic=5.0,
        )
        gamma_dil = metrics_dil["gamma_dilation"]
        time_regime = metrics_dil["time_regime"]

        mass_eff, inertial_idx = _effective_mass_and_inertia(
            kappa_eff,
            entropy_eff,
            gamma_dil,
            barrier_occupancy=1.0,
            m0=1.0,
            w_kappa=1.0,
            w_H=0.5,
        )

        rec = {
            "family": "SAT_crit_n",
            "name": name,
            "n_vars": n_vars,
            "num_clauses": num_clauses,
            "kappa_eff": kappa_eff,
            "entropy_eff": entropy_eff,
            "V0": V0,
            "a_min": a_min,
            "p_tunnel": p_t,
            "E_N": e_n,
            "P_success": p_s,
            "gamma_dilation": gamma_dil,
            "time_regime": time_regime,
            "mass_eff": mass_eff,
            "inertial_idx": inertial_idx,
            "decision_label": label,
        }
        records.append(rec)

    try:
        enriched = loventre_attach_global_decision_to_family(
            records, family_name="SAT_crit_n"
        )
    except Exception:
        enriched = records

    for r in enriched:
        gd = r.get("loventre_global") or {}
        g_dec = gd.get("global_decision", "N/A") or "N/A"
        g_col = gd.get("global_color", "N/A") or "N/A"
        g_scr = gd.get("global_score", 0.0) or 0.0

        print(
            f"{r['name']:10s}  "
            f"{r['n_vars']:6d}  "
            f"{r['num_clauses']:7d}  "
            f"{r['kappa_eff']:8.3f}  "
            f"{r['entropy_eff']:8.3f}  "
            f"{r['V0']:6.4f}  "
            f"{r['a_min']:6.2f}  "
            f"{r['p_tunnel']:11.3e}  "
            f"{r['E_N']:11.3e}  "
            f"{r['P_success']:9.3e}  "
            f"{r['gamma_dilation']:10.2f}  "
            f"{r['mass_eff']:8.3f}  "
            f"{r['inertial_idx']:11.3f}  "
            f"{r['time_regime']:13s}  "
            f"{r['decision_label']:20s}  "
            f"{g_dec:6s}  "
            f"{g_col:5s}  "
            f"{g_scr:6.3f}"
        )

    print()
    print("Nota meta-portafoglio SAT_crit_n:")
    print("  - κ_eff, H_eff, V0 e a_min crescono con n_vars,")
    print("    facendo esplodere E[N] e collassare P_success con N_budget polinomiale.")
    print("  - La massa informazionale effettiva e l'indice inerziale seguono la stessa tendenza,")
    print("    mostrando una dinamica sempre più pesante e time_hyperbolic.")
    print("  - Fornisce una famiglia NP_like-critica Loventre per SAT,")
    print("    da confrontare con SAT toy e TSP toy P-like/precritici,")
    print("    e con TSP_crit_n come famiglia critica geometrica a tour.")
    print()
'''

    new_src, n_tsp = pattern_tsp.subn(block_tsp + "\n", src, count=1)
    if n_tsp == 0:
        print(
            "[Loventre] ATTENZIONE: non sono riuscito a patchare print_tsp_critical_portfolio "
            "(pattern non trovato)."
        )
        return

    new_src, n_sat = pattern_sat.subn(block_sat + "\n", new_src, count=1)
    if n_sat == 0:
        print(
            "[Loventre] ATTENZIONE: non sono riuscito a patchare print_sat_critical_portfolio "
            "(pattern non trovato)."
        )
        return

    target.write_text(new_src, encoding="utf-8")
    print(
        "[Loventre] print_tsp_critical_portfolio e print_sat_critical_portfolio "
        "aggiornate con uso di loventre_global_decision (via helper Loventre) per famiglie critiche."
    )


if __name__ == "__main__":
    main()

