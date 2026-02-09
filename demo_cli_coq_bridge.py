#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
===== LOVENTRE ENGINE — CLI Coq Bridge DEMO V6 =====
Genera tutte le combinazioni canoniche kappa × entropy
e salva JSON bridge verso Coq.
"""

import os
import json
from loventre_meta_engine import run_loventre_meta_engine

OUTPUT_DIR = os.path.join(os.getcwd(), "JSON_IO", "LMetrics_v6_cli_bridge")
os.makedirs(OUTPUT_DIR, exist_ok=True)

# Definizione griglie canoniche di kappa ed entropy
kappa_values = [3.0, 2.7, 2.4, 2.1, 1.8, 1.5, 1.2, 0.9, 0.6, 0.3, 0.0, -0.3, -0.6, -0.9, -1.2,
                -1.5, -1.8, -2.1, -2.4, -2.7, -3.0]
entropy_values = [None, 1.0, 4.0]  # griglia demo canonica

def run_demo():
    case_counter = 1
    for e in entropy_values:
        for k in kappa_values:
            metrics = run_loventre_meta_engine(kappa=k, entropy=e)
            json_filename = f"lmetrics_v6_cli_case_{case_counter}.json"
            json_path = os.path.join(OUTPUT_DIR, json_filename)
            with open(json_path, "w", encoding="utf-8") as f:
                json.dump(metrics, f, indent=2)
            
            k_display = "None" if k is None else f"{k:.1f}"
            e_display = "None" if e is None else f"{e:.1f}"
            decision = metrics.get("loventre_global_decision", metrics.get("decision", "UNKNOWN"))
            color = metrics.get("loventre_global_color", metrics.get("color", "UNKNOWN"))
            score = metrics.get("loventre_global_score", metrics.get("score", 0.0))
            risk = metrics.get("risk_index", metrics.get("risk", 0.0))

            print(f"[Loventre Meta Engine] run_loventre_meta_engine called with kappa={k_display}, entropy={e_display}")
            print(f"[CASE {case_counter}] kappa={k_display} entropy={e_display}")
            print(f"  → decision={decision} color={color} score={score} risk={risk}\n")
            print(f"  ✔ {json_filename}\n")
            
            case_counter += 1

    print("\n===== EXPORT COMPLETATO =====")
    print(f"Cartella: {OUTPUT_DIR}\n")
    print("===== END CLI Coq Bridge DEMO V6 =====")

if __name__ == "__main__":
    run_demo()

