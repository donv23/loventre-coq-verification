from __future__ import annotations

from typing import Dict, List

from loventre_meta_decision_engine import meta_decide_instance_with_mass as meta_decide_instance


def build_history_regular() -> List[Dict[str, float]]:
    """
    History P-like: complessita' moderata, entropia moderata, niente barriera seria.
    """
    history = []
    for t in range(12):
        C_t = 0.1 * t
        H_t = 0.05 * (t % 4)
        history.append({"C": C_t, "H": H_t})
    return history


def build_history_precritical() -> List[Dict[str, float]]:
    """
    History quasi-critica: C e H crescono, una porzione restando sopra soglia, ma non estrema.
    """
    history = []
    for t in range(15):
        C_t = 0.2 * t
        H_t = 0.1 * (t % 5) + 0.3
        history.append({"C": C_t, "H": H_t})
    return history


def build_history_critical() -> List[Dict[str, float]]:
    """
    History critica: C e H crescono aggressivamente, con molti step ad alta barriera.
    """
    history = []
    for t in range(18):
        C_t = 0.4 * t
        H_t = 0.2 * (t % 6) + 0.5
        history.append({"C": C_t, "H": H_t})
    return history


def run_scenario(name: str, history: List[Dict[str, float]], E: float) -> None:
    result = meta_decide_instance(
        history,
        E=E,
        alpha=1.0,
        beta=1.0,
        G_L=1.0,
        lambda_L=0.0,
        V0=None,
        V0_quantile=0.85,
        p_target=0.1,
        gamma_cap=100.0,
    )

    horizon_info = result["horizon_info"]

    print()
    print("==================================================")
    print(f"=== META-DECISIONE LOVENTRE – {name:<10s} ===")
    print("==================================================")
    print(f"V0 stimato:             {result['V0']}")
    print(f"a_min (spessore):       {result['a_min']}")
    print(f"E attuale:              {result['E']}")
    print(f"p_tunnel:               {result['p_tunnel']:.3e}")
    print(f"E_min_for_p_target:     {result.get('E_min_for_p_target')}")
    print(f"energy_ratio E/E_min:   {result.get('energy_ratio')}")
    print(f"energy_regime:          {result.get('energy_regime')}")
    print(f"gamma_dilation:         {result.get('gamma_dilation')}")
    print(f"time_regime:            {result.get('time_regime')}")
    print(f"classificazione (spaziale): {result.get('classification')}")
    print(f"barrier_occupancy:      {result.get('barrier_occupancy')}")
    print(f"mass_mean:              {result.get('mass_mean')}")
    print(f"mass_max:               {result.get('mass_max')}")
    print(f"inertial_difficulty_index: {result.get('inertial_difficulty_index')}")
    print(f"Orizzonte rilevato:     {horizon_info.get('horizon_detected')}")
    print(f"Rischio buco nero:      {horizon_info.get('black_hole_risk')}")
    print(f"Strategia locale:       {result.get('strategy')}")
    print(f"Meta-label:             {result.get('meta_label')}")
    print("--- Spiegazione Loventre ---")
    print(result.get("meta_explanation", ""))


def main() -> None:
    E = 1.5  # energia di prova

    hist_reg = build_history_regular()
    hist_pre = build_history_precritical()
    hist_crit = build_history_critical()

    run_scenario("REGOLARE", hist_reg, E=E)
    run_scenario("PRECRITICAL", hist_pre, E=E)
    run_scenario("CRITICAL", hist_crit, E=E)


if __name__ == "__main__":
    main()