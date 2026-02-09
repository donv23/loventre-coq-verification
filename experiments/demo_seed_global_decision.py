"""
demo_seed_global_decision.py

Demo aggiornata – Loventre Engine dicembre 2025
----------------------------------------------
Esegue un check singolo di "global decision" su un witness seed canonico
utilizzando il Policy Bridge v3 reale (apply_policy_bridge_to_metrics).
"""

from __future__ import annotations
import json
from pathlib import Path
from loventre_policy_bridge import apply_policy_bridge_to_metrics


def main() -> None:
    print("===================================================================")
    print("=== LOVENTRE DEMO – Seed Global Decision (v3 Policy Bridge)     ===")
    print("===================================================================\n")

    base_dir = Path(__file__).resolve().parent
    metrics_path = base_dir / "metrics_seed11_cli_demo.json"

    if not metrics_path.exists():
        print(f"[WARN] File {metrics_path.name} non trovato – demo saltata.")
        return

    data = json.loads(metrics_path.read_text(encoding="utf-8"))
    print(f"[INFO] Caricato metrics JSON: {metrics_path.name}")

    # Applica il Policy Bridge reale (shim)
    data = apply_policy_bridge_to_metrics(data)

    print("\n>>> BLOCCO GLOBAL DECISION (post-policy)")
    print(f"  global_decision_label : {data.get('global_decision_label')}")
    print(f"  global_decision_score : {data.get('global_decision_score')}")
    print(f"  meta_explanation       : {data.get('global_meta_explanation')}")

    print("\n>>> META INFORMAZIONI")
    print(f"  meta_label  : {data.get('meta_label', '?')}")
    print(f"  risk_class  : {data.get('risk_class', '?')}")
    print(f"  horizon_flag: {data.get('horizon_flag', '?')}")

    print("\n=== FINE DEMO SEED GLOBAL DECISION ===")


if __name__ == "__main__":
    main()

