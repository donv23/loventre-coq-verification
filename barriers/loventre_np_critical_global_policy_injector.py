#!/usr/bin/env python3
"""
loventre_np_critical_global_policy_injector.py

Scopo:
  - Prendere i JSON NP_critici (SAT_crit16, TSP_crit28),
  - aggiungere una Policy globale coerente con il Teorema:
      * NP_like_crit_complexity => NON SAFE, NON GREEN,
  - scrivere nuovi file *_with_global.json.

Assunzioni:
  - Esistono nella root:
      metrics_SAT_crit16_demo.json
      metrics_TSP_crit28_demo.json
  - Ogni file contiene già campi come family, meta_label, risk_class, horizon_flag, ecc.
"""

import json
from pathlib import Path


ROOT = Path(__file__).resolve().parent


NP_CRITICAL_CONFIGS = [
    {
        "input": "metrics_SAT_crit16_demo.json",
        "output": "metrics_SAT_crit16_demo_with_global.json",
        "family": "SAT_crit16",
    },
    {
        "input": "metrics_TSP_crit28_demo.json",
        "output": "metrics_TSP_crit28_demo_with_global.json",
        "family": "TSP_crit28",
    },
]


def make_global_payload(data, *, family: str):
    """
    Restituisce una nuova dict con i campi di Policy globale
    sovrascritti / aggiunti in modo coerente con il cono NP_critico:

      - loventre_global_decision = "GD_withdraw"   (esplicitamente NON SAFE)
      - loventre_global_color    = "GC_red"        (esplicitamente NON GREEN)
      - loventre_global_score    = 0.0             (score minimale in [0,1])
    """
    new_data = dict(data)  # copia superficiale

    new_data["loventre_global_decision"] = "GD_withdraw"
    new_data["loventre_global_color"] = "GC_red"
    new_data["loventre_global_score"] = 0.0

    # Nota: non tocchiamo meta_label, risk_class, horizon_flag, ecc.
    # Ci aspettiamo che per questi JSON valga già:
    #   risk_class = risk_NP_like_black_hole
    #   horizon_flag = true
    # così che ricadano nel profilo NP_like_crit_complexity lato Python/Coq.

    return new_data


def main():
    print("[Loventre] NP-critical global policy injector")
    print(f"Root: {ROOT}")

    for cfg in NP_CRITICAL_CONFIGS:
        in_path = ROOT / cfg["input"]
        out_path = ROOT / cfg["output"]

        if not in_path.exists():
            print(f"[SKIP] File di input non trovato: {in_path.name}")
            continue

        print(f"[INFO] Leggo {in_path.name} ...")
        with in_path.open("r", encoding="utf-8") as f:
            data = json.load(f)

        new_data = make_global_payload(data, family=cfg["family"])

        with out_path.open("w", encoding="utf-8") as f:
            json.dump(new_data, f, indent=2, sort_keys=True)

        decision = new_data.get("loventre_global_decision", "?")
        color = new_data.get("loventre_global_color", "?")
        score = new_data.get("loventre_global_score", "?")

        print(
            f"[OK] Scritto {out_path.name} "
            f"(decision={decision}, color={color}, score={score})"
        )

    print("[DONE] Iniezione Policy globale per NP_critici completata (dove possibile).")


if __name__ == "__main__":
    main()

