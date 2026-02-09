"""
loventre_einstein_layers_test_lab.py

Smoke/regression test per i layer "alla Einstein" del Loventre Engine:

1) Geometria di base (curvatura, potenziale, barriera, tunneling).
2) Time dilation e time_regime.
3) Energia minima E_min_for_p_target e energy_regime.
4) Massa informazionale e inertial_difficulty_index.
5) Orizzonte di complessità / quasi buco nero (wrapper mass-aware).
6) Meta-decision engine con massa (meta_decide_instance_with_mass).
7) Lensing lab (script e output base).
8) Meta–portafogli TSP_crit_n e SAT_crit_n con massa effettiva e inerzia.
"""

import math
import subprocess
import sys
from pathlib import Path


failures = 0


def check(cond: bool, label: str) -> None:
    global failures
    if cond:
        print(f"[OK]   {label}")
    else:
        print(f"[FAIL] {label}")
        failures += 1


def test_geometry_time_energy_mass() -> None:
    """
    Test 1–5: geometria, tempo, energia, massa, orizzonte (funzioni base).
    """
    print("\n=== TEST 1: geometry + time + energy + mass + horizon ===")
    try:
        from loventre_instance_analysis import (
            analyze_instance,
            enrich_metrics_with_time_dilation,
            enrich_metrics_with_energy_requirements,
            enrich_metrics_with_mass,
            detect_complexity_horizon,
        )
    except Exception as exc:
        check(False, f"import da loventre_instance_analysis fallito: {exc}")
        return

    # History "facile": C, H moderati
    history_easy = [
        {"C": 0.2, "H": 0.1},
        {"C": 0.3, "H": 0.2},
        {"C": 0.4, "H": 0.3},
        {"C": 0.3, "H": 0.2},
        {"C": 0.2, "H": 0.1},
    ]

    # History "dura": C e H più grandi
    history_hard = [
        {"C": 1.0, "H": 0.8},
        {"C": 1.2, "H": 0.9},
        {"C": 1.4, "H": 1.0},
        {"C": 1.3, "H": 0.9},
        {"C": 1.1, "H": 0.8},
    ]

    # E alta per la versione facile, E bassa per quella dura
    E_easy = 2.0
    E_hard = 0.2

    try:
        metrics_easy = analyze_instance(history_easy, E_easy, V0_quantile=0.8)
        metrics_hard = analyze_instance(history_hard, E_hard, V0_quantile=0.8)
    except TypeError:
        # fallback se la firma di analyze_instance è diversa e richiede argomenti nominati
        metrics_easy = analyze_instance(history=history_easy, E=E_easy, V0_quantile=0.8)
        metrics_hard = analyze_instance(history=history_hard, E=E_hard, V0_quantile=0.8)

    # Check base: V0, a_min, p_tunnel presenti
    for name, m in (("easy", metrics_easy), ("hard", metrics_hard)):
        check("V0" in m, f"[{name}] V0 presente in metrics")
        check("a_min" in m, f"[{name}] a_min presente in metrics")
        check("p_tunnel" in m, f"[{name}] p_tunnel presente in metrics")

    # Arricchimento tempo
    metrics_easy = enrich_metrics_with_time_dilation(
        metrics_easy,
        gamma_cap=100.0,
        gamma_threshold_euclidean=2.0,
        gamma_threshold_hyperbolic=5.0,
    )
    metrics_hard = enrich_metrics_with_time_dilation(
        metrics_hard,
        gamma_cap=100.0,
        gamma_threshold_euclidean=2.0,
        gamma_threshold_hyperbolic=5.0,
    )

    # Arricchimento energia
    metrics_easy = enrich_metrics_with_energy_requirements(metrics_easy, 0.1)
    metrics_hard = enrich_metrics_with_energy_requirements(metrics_hard, 0.1)

    # Arricchimento massa
    metrics_easy = enrich_metrics_with_mass(
        metrics_easy,
        history_easy,
        m0=1.0,
        w_C=1.0,
        w_H=0.5,
    )
    metrics_hard = enrich_metrics_with_mass(
        metrics_hard,
        history_hard,
        m0=1.0,
        w_C=1.0,
        w_H=0.5,
    )

    # 1) hard deve avere barriera più alta o simile
    if "V0" in metrics_easy and "V0" in metrics_hard:
        check(
            metrics_hard["V0"] >= metrics_easy["V0"],
            "V0_hard >= V0_easy (barriera più alta o uguale per history hard)",
        )

    # 2) p_tunnel hard deve essere più piccolo
    p_easy = metrics_easy.get("p_tunnel")
    p_hard = metrics_hard.get("p_tunnel")
    if isinstance(p_easy, (int, float)) and isinstance(p_hard, (int, float)):
        check(
            p_hard < p_easy,
            "p_tunnel(hard) < p_tunnel(easy) (tunneling più raro sul caso hard)",
        )

    # 3) gamma_dilation hard > easy
    g_easy = metrics_easy.get("gamma_dilation")
    g_hard = metrics_hard.get("gamma_dilation")
    if isinstance(g_easy, (int, float)) and isinstance(g_hard, (int, float)):
        check(
            g_hard > g_easy,
            "gamma_dilation(hard) > gamma_dilation(easy) (tempo più dilatato sul caso hard)",
        )

    # 4) E_min_for_p_target: l'istanza hard deve chiedere più energia
    e_min_easy = metrics_easy.get("E_min_for_p_target")
    e_min_hard = metrics_hard.get("E_min_for_p_target")
    if isinstance(e_min_easy, (int, float)) and isinstance(e_min_hard, (int, float)):
        check(
            e_min_hard >= e_min_easy,
            "E_min_for_p_target(hard) >= E_min_for_p_target(easy)",
        )

    # 5) Massa e inerzia: hard deve avere massa media maggiore e inerzia maggiore
    m_mean_easy = metrics_easy.get("mass_mean")
    m_mean_hard = metrics_hard.get("mass_mean")
    if isinstance(m_mean_easy, (int, float)) and isinstance(m_mean_hard, (int, float)):
        check(
            m_mean_hard > m_mean_easy,
            "mass_mean(hard) > mass_mean(easy)",
        )

    inert_easy = metrics_easy.get("inertial_difficulty_index")
    inert_hard = metrics_hard.get("inertial_difficulty_index")
    if isinstance(inert_easy, (int, float)) and isinstance(inert_hard, (int, float)):
        check(
            inert_hard > inert_easy,
            "inertial_difficulty_index(hard) > inertial_difficulty_index(easy)",
        )

    # 6) Wrapper orizzonte / quasi buco nero: costruiamo un metrics artificiale
    # con p_tunnel molto piccolo, gamma alta, inerzia alta e occupazione di barriera decente.
    metrics_horizon = dict(metrics_hard)
    metrics_horizon["p_tunnel"] = 1e-8
    metrics_horizon["gamma_dilation"] = max(float(metrics_horizon.get("gamma_dilation", 0.0)), 20.0)
    metrics_horizon["inertial_difficulty_index"] = max(
        float(metrics_horizon.get("inertial_difficulty_index", 0.0)), 15.0
    )
    metrics_horizon["barrier_occupancy"] = max(
        float(metrics_horizon.get("barrier_occupancy", 0.0)), 0.25
    )

    metrics_horizon = detect_complexity_horizon(metrics_horizon)
    check(
        bool(metrics_horizon.get("horizon_detected", False)),
        "detect_complexity_horizon: horizon_detected True in regime quasi-buco-nero",
    )
    check(
        bool(metrics_horizon.get("black_hole_risk", False)),
        "detect_complexity_horizon: black_hole_risk True in regime quasi-buco-nero",
    )


def test_meta_decision_with_mass() -> None:
    """
    Test 6: meta_decide_instance_with_mass (core Einstein-Loventre).
    """
    print("\n=== TEST 2: meta_decide_instance_with_mass ===")
    try:
        from loventre_meta_decision_engine import meta_decide_instance_with_mass
    except Exception as exc:
        check(False, f"import meta_decide_instance_with_mass fallito: {exc}")
        return

    # History easy/hard come prima (riusiamo gli stessi pattern)
    history_easy = [
        {"C": 0.2, "H": 0.1},
        {"C": 0.3, "H": 0.2},
        {"C": 0.4, "H": 0.3},
        {"C": 0.3, "H": 0.2},
        {"C": 0.2, "H": 0.1},
    ]

    history_hard = [
        {"C": 1.0, "H": 0.8},
        {"C": 1.2, "H": 0.9},
        {"C": 1.4, "H": 1.0},
        {"C": 1.3, "H": 0.9},
        {"C": 1.1, "H": 0.8},
    ]

    res_easy = meta_decide_instance_with_mass(history_easy, E=2.0, V0_quantile=0.85, p_target=0.1)
    res_hard = meta_decide_instance_with_mass(history_hard, E=0.2, V0_quantile=0.85, p_target=0.1)

    ml_easy = res_easy.get("meta_label")
    ml_hard = res_hard.get("meta_label")

    check("mass_regime" in res_easy, "mass_regime presente in meta_decision (easy)")
    check("mass_regime" in res_hard, "mass_regime presente in meta_decision (hard)")

    # Easy dovrebbe essere P_like_accessibile / zona_intermedia, non NP_like_critico
    if isinstance(ml_easy, str):
        check(
            ml_easy != "NP_like_critico",
            f"meta_label(easy) non è NP_like_critico (è {ml_easy})",
        )

    # Hard non dovrebbe essere P_like_accessibile
    if isinstance(ml_hard, str):
        check(
            ml_hard != "P_like_accessibile",
            f"meta_label(hard) non è P_like_accessibile (è {ml_hard})",
        )

    # Difficoltà e dilatazione maggiori sul caso hard
    g_easy = res_easy.get("gamma_dilation")
    g_hard = res_hard.get("gamma_dilation")
    if isinstance(g_easy, (int, float)) and isinstance(g_hard, (int, float)):
        check(
            g_hard >= g_easy,
            "gamma_dilation(hard) >= gamma_dilation(easy) nella meta-decisione",
        )

    inert_easy = res_easy.get("inertial_difficulty_index")
    inert_hard = res_hard.get("inertial_difficulty_index")
    if isinstance(inert_easy, (int, float)) and isinstance(inert_hard, (int, float)):
        check(
            inert_hard >= inert_easy,
            "inertial_difficulty_index(hard) >= inertial_difficulty_index(easy) nella meta-decisione",
        )

    # Spiegazione con Strato di massa Loventre
    expl_hard = res_hard.get("meta_explanation", "")
    check(
        "Strato di massa Loventre" in expl_hard,
        "meta_explanation(hard) contiene lo 'Strato di massa Loventre'",
    )


def test_lensing_lab() -> None:
    """
    Test 7: loventre_lensing_geodesic_lab.py gira e produce output con colonna Lens.
    """
    print("\n=== TEST 3: lensing geodesic lab ===")
    script = Path("loventre_lensing_geodesic_lab.py")
    if not script.exists():
        check(False, "loventre_lensing_geodesic_lab.py non trovato")
        return

    try:
        result = subprocess.run(
            ["python3", str(script)],
            check=True,
            capture_output=True,
            text=True,
        )
    except Exception as exc:
        check(False, f"esecuzione loventre_lensing_geodesic_lab.py fallita: {exc}")
        return

    out = result.stdout
    check("Loventre Lensing Geodesic Walk Lab" in out, "header del lensing lab presente")
    check("Lens" in out, "colonna 'Lens' presente nell'output del lab")
    check("lenti attive" in out or "Lenti attive" in out, "sezione lenti attive presente")


def _parse_tsp_section(output_lines: list[str]) -> tuple[list[float], list[float], list[float]]:
    mass_vals = []
    inert_vals = []
    gamma_vals = []

    in_tsp = False
    for line in output_lines:
        if "LOVENTRE META-PORTFOLIO – TSP_crit_n" in line:
            in_tsp = True
            continue
        if in_tsp and line.startswith("Nota meta-portafoglio TSP_crit_n"):
            break
        if not in_tsp:
            continue
        stripped = line.strip()
        if not stripped:
            continue
        if stripped.startswith("n_cities") or stripped.startswith("-"):
            continue
        # line dati: inizia tipicamente con un numero di città
        tokens = stripped.split()
        if not tokens:
            continue
        # primo token dovrebbe essere un intero (n_cities)
        try:
            int(tokens[0])
        except ValueError:
            continue

        # tokens: 0=n_cities, 1=kappa, 2=entropy, 3=V0, 4=a_min, 5=p_t, 6=E[N], 7=P_success,
        # 8=gamma_dil, 9=mass_eff, 10=inertial_idx, 11=time_regime, ...
        if len(tokens) >= 11:
            try:
                gamma_vals.append(float(tokens[8]))
                mass_vals.append(float(tokens[9]))
                inert_vals.append(float(tokens[10]))
            except ValueError:
                continue

    return gamma_vals, mass_vals, inert_vals


def _parse_sat_section(output_lines: list[str]) -> tuple[list[float], list[float], list[float]]:
    mass_vals = []
    inert_vals = []
    gamma_vals = []

    in_sat = False
    for line in output_lines:
        if "LOVENTRE META-PORTFOLIO – SAT_crit_n" in line:
            in_sat = True
            continue
        if in_sat and line.startswith("Nota meta-portafoglio SAT_crit_n"):
            break
        if not in_sat:
            continue
        stripped = line.strip()
        if not stripped:
            continue
        if stripped.startswith("name") or stripped.startswith("-"):
            continue
        tokens = stripped.split()
        if not tokens:
            continue
        # primo token è il nome (es. sat_crit4)
        if len(tokens) >= 13:
            try:
                gamma_vals.append(float(tokens[10]))
                mass_vals.append(float(tokens[11]))
                inert_vals.append(float(tokens[12]))
            except ValueError:
                continue

    return gamma_vals, mass_vals, inert_vals


def test_critical_portfolios() -> None:
    """
    Test 8: loventre_meta_portfolio_lab.py con TSP_crit_n e SAT_crit_n + massa effettiva.
    """
    print("\n=== TEST 4: critical portfolios TSP_crit_n + SAT_crit_n ===")
    script = Path("loventre_meta_portfolio_lab.py")
    if not script.exists():
        check(False, "loventre_meta_portfolio_lab.py non trovato")
        return

    try:
        result = subprocess.run(
            ["python3", str(script)],
            check=True,
            capture_output=True,
            text=True,
        )
    except Exception as exc:
        check(False, f"esecuzione loventre_meta_portfolio_lab.py fallita: {exc}")
        return

    out_lines = result.stdout.splitlines()

    # TSP_crit_n
    gamma_tsp, mass_tsp, inert_tsp = _parse_tsp_section(out_lines)
    check(len(mass_tsp) >= 2, f"TSP_crit_n: trovate {len(mass_tsp)} righe dati (>=2)")
    if mass_tsp:
        tsp_mass_monotone = all(mass_tsp[i] >= mass_tsp[i - 1] - 1e-9 for i in range(1, len(mass_tsp)))
        tsp_inert_monotone = all(inert_tsp[i] >= inert_tsp[i - 1] - 1e-9 for i in range(1, len(inert_tsp)))
        tsp_gamma_monotone = all(gamma_tsp[i] >= gamma_tsp[i - 1] - 1e-9 for i in range(1, len(gamma_tsp)))
        check(tsp_mass_monotone, "TSP_crit_n: mass_eff non decrescente con n_cities")
        check(tsp_inert_monotone, "TSP_crit_n: inert_idx non decrescente con n_cities")
        check(tsp_gamma_monotone, "TSP_crit_n: gamma_dil non decrescente con n_cities")

    # SAT_crit_n
    gamma_sat, mass_sat, inert_sat = _parse_sat_section(out_lines)
    check(len(mass_sat) >= 2, f"SAT_crit_n: trovate {len(mass_sat)} righe dati (>=2)")
    if mass_sat:
        sat_mass_monotone = all(mass_sat[i] >= mass_sat[i - 1] - 1e-9 for i in range(1, len(mass_sat)))
        sat_inert_monotone = all(inert_sat[i] >= inert_sat[i - 1] - 1e-9 for i in range(1, len(inert_sat)))
        sat_gamma_monotone = all(gamma_sat[i] >= gamma_sat[i - 1] - 1e-9 for i in range(1, len(gamma_sat)))
        check(sat_mass_monotone, "SAT_crit_n: mass_eff non decrescente con n_vars")
        check(sat_inert_monotone, "SAT_crit_n: inert_idx non decrescente con n_vars")
        check(sat_gamma_monotone, "SAT_crit_n: gamma_dil non decrescente con n_vars")


def main() -> None:
    test_geometry_time_energy_mass()
    test_meta_decision_with_mass()
    test_lensing_lab()
    test_critical_portfolios()

    print("\n=== SUMMARY Einstein-Loventre layers ===")
    if failures == 0:
        print("TUTTI I TEST SONO PASSATI ✅")
    else:
        print(f"Numero di test falliti: {failures}")
    sys.exit(0 if failures == 0 else 1)


if __name__ == "__main__":
    main()
