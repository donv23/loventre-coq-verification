from __future__ import annotations

import json
import sys
from pathlib import Path
from typing import Any, Dict, List

from loventre_meta_decision_engine import (
    meta_decide_instance_with_mass as meta_decide_instance,
)
from loventre_theory_bridge_seed import print_einstein_loventre_quick_summary


History = List[Dict[str, float]]


def _load_history_from_json(path: Path) -> History:
    """
    Carica una history da file JSON del tipo:

        [
          {"C": 0.1, "H": 0.2},
          {"C": 0.2, "H": 0.3},
          ...
        ]
    """
    raw = json.loads(path.read_text())
    if not isinstance(raw, list):
        raise ValueError("Il file JSON deve contenere una lista di stati.")

    history: History = []
    for idx, el in enumerate(raw):
        if not isinstance(el, dict):
            raise ValueError(f"Elemento in posizione {idx} non e' un dict.")
        C_val = float(el.get("C", 0.0))
        H_val = float(el.get("H", 0.0))
        history.append({"C": C_val, "H": H_val})

    if not history:
        raise ValueError("History vuota nel file JSON.")

    return history


def _safe_get(d: Dict[str, Any], key: str, default: Any = None) -> Any:
    return d.get(key, default)


def _print_scenario_header(title: str) -> None:
    bar = "=" * 70
    print()
    print(bar)
    print(title)
    print(bar)


def run_scenario(
    title: str,
    history: History,
    E: float,
    V0_q: float,
    p_target: float,
) -> None:
    _print_scenario_header(title)
    print(f"E = {E} | V0_quantile = {V0_q} | p_target = {p_target}")
    print()

    result: Dict[str, Any] = meta_decide_instance(
        history,
        E=E,
        alpha=1.0,
        beta=1.0,
        G_L=1.0,
        lambda_L=0.0,
        V0=None,
        V0_quantile=V0_q,
        p_target=p_target,
        gamma_cap=100.0,
    )

    # --- QUICK SUMMARY ---
    print("--- QUICK EINSTEIN–LOVENTRE SUMMARY ---")
    print_einstein_loventre_quick_summary(result)
    print()

    # --- INDICI CHIAVE ---
    meta_label = _safe_get(result, "meta_label")
    risk_index = _safe_get(result, "risk_index")
    risk_class = _safe_get(result, "risk_class")
    time_regime = _safe_get(result, "time_regime")
    energy_regime = _safe_get(result, "energy_regime")
    mass_regime = _safe_get(result, "mass_regime")
    p_tunnel = _safe_get(result, "p_tunnel")
    gamma_dil = _safe_get(result, "gamma_dilation")
    hawking_regime = _safe_get(result, "hawking_regime")
    planck_regime = _safe_get(result, "planck_regime")

    print("--- INDICI CHIAVE ---")
    print(f"meta_label      : {meta_label}")
    print(f"risk_index      : {risk_index} ({risk_class})")
    print(f"time_regime     : {time_regime}")
    print(f"energy_regime   : {energy_regime}")
    print(f"mass_regime     : {mass_regime}")
    print(f"p_tunnel        : {p_tunnel}")
    print(f"gamma_dilation  : {gamma_dil}")
    print(f"hawking_regime  : {hawking_regime}")
    print(f"planck_regime   : {planck_regime}")
    print()

    # --- LOVENTRE POLICY BRIDGE (estratto dai metrics) ---
    strategy_decision = _safe_get(result, "policy_strategy")
    energy_policy = _safe_get(result, "policy_energy")
    comment = _safe_get(result, "policy_comment")

    print("--- LOVENTRE POLICY BRIDGE (estratto dai metrics) ---")
    print(f"strategy_decision : {strategy_decision}")
    print(f"energy_policy     : {energy_policy}")
    print(f"comment           : {comment}")
    print()

    # --- META-EXPLANATION COMPLETA ---
    explanation = _safe_get(result, "meta_explanation", "")
    print("--- META-EXPLANATION COMPLETA ---")
    print(explanation)
    print()


def main() -> None:
    # history.json opzionale come primo argomento; se manca usiamo esempio_history.json
    if len(sys.argv) >= 2:
        history_path_str = sys.argv[1]
        history_path = Path(history_path_str)
    else:
        print("[INFO] Nessun file history specificato, uso esempio_history.json")
        history_path = Path("esempio_history.json")

    history = _load_history_from_json(history_path)

    # SCENARIO 1 – P-like / energia abbondante
    run_scenario(
        "SCENARIO 1 – P-like / energia abbondante",
        history,
        E=3.0,
        V0_q=0.6,
        p_target=0.05,
    )

    # SCENARIO 2 – quasi-critico / metastabile
    run_scenario(
        "SCENARIO 2 – quasi-critico / metastabile",
        history,
        E=1.5,
        V0_q=0.85,
        p_target=0.1,
    )

    # SCENARIO 3 – NP_like supercritico / quasi buco nero
    run_scenario(
        "SCENARIO 3 – NP_like supercritico / quasi buco nero",
        history,
        E=0.7,
        V0_q=0.95,
        p_target=0.2,
    )


if __name__ == "__main__":
    main()

