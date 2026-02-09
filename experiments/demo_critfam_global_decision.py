"""
demo_critfam_global_decision.py

Demo aggiornata – Loventre Engine dicembre 2025
----------------------------------------------
Esegue un check di "global decision" su SAT/TSP critici,
utilizzando il Policy Bridge v3 reale (apply_policy_bridge_to_metrics).
"""

from __future__ import annotations
import json
from pathlib import Path
from loventre_policy_bridge import apply_policy_bridge_to_metrics


def main() -> None:
    print("===================================================================")
    print("=== LOVENTRE DEMO – Critical Family Global Decision (v3 Bridge) ===")
    print("===================================================================\n")

    base_dir = Path(__file__).resolve().parent
    targets = [
        "metrics_SAT_crit16_demo.json",
        "metrics_TSP_crit28_demo.json",
    ]

    for name in targets:
        path = base_dir / name
        print(f"\n>>> Analisi {name}")
        if not path.exists():
            print(f"  [WARN] File {name} non trovato – skip.")
            continue

        data = json.loads(path.read_text(encoding="utf-8"))
        data = apply_policy_bridge_to_metrics(data)

        print(f"  global_decision_label : {data.get('global_decision_label')}")
        print(f"  global_decision_score : {data.get('global_decision_score')}")
        print(f"  meta_explanation       : {data.get('global_meta_explanation')}")
        print(f"  risk_class             : {data.get('risk_class', '?')}")
        print(f"  meta_label             : {data.get('meta_label', '?')}")
        print(f"  horizon_flag           : {data.get('horizon_flag', '?')}")

    print("\n=== FINE DEMO CRITFAM GLOBAL DECISION ===")


if __name__ == "__main__":
    main()

