#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
run_lab_suite_v12.py
--------------------------------------------
Mini suite per testare LAB V12 (sandbox).
Non tocca JSON canonici.
"""

import os
import sys

# === AGGIUNTA CRUCIALE ===
ROOT = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(ROOT)  # cartella loventre_engine_clean_seed
if ROOT not in sys.path:
    sys.path.append(ROOT)

from LAB.loventre_lab_metrics_v12 import compute_lab_metrics_v12
from LAB.loventre_lab_pipeline_v12 import run_lab_pipeline_v12
from LAB.loventre_lab_bus_v12 import run_lab_bus_v12
from LAB.loventre_lab_policy_v12 import suggest_lab_policy_v12
from LAB.loventre_lab_decision_v12 import run_lab_decision_v12
from LAB.loventre_lab_bridge_v12 import decide_lab_bridge_v12
from LAB.loventre_lab_entrypoint_v12 import run_lab_entrypoint_v12
from LAB.loventre_lab_export_v12 import run_lab_export_v12


def safe_run(name, fn):
    try:
        fn()
        print(f"[ OK ] {name}")
        return True
    except Exception as e:
        print(f"[ERR] {name} → {e}")
        return False


def run_suite():
    print("\n\n===== LAB V12 MINI SUITE =====\n")

    results = [
        safe_run("loventre_lab_metrics_v12.compute_lab_metrics_v12",
                 lambda: compute_lab_metrics_v12(0.5)),
        safe_run("loventre_lab_pipeline_v12.run_lab_pipeline_v12",
                 lambda: run_lab_pipeline_v12(kappa=0.5)),
        safe_run("loventre_lab_bus_v12.run_lab_bus_v12",
                 lambda: run_lab_bus_v12(kappa_eff=0.5)),
        safe_run("loventre_lab_policy_v12.suggest_lab_policy_v12",
                 lambda: suggest_lab_policy_v12(0.5)),
        safe_run("loventre_lab_decision_v12.run_lab_decision_v12",
                 lambda: run_lab_decision_v12(kappa_eff=0.5)),
        safe_run("loventre_lab_bridge_v12.decide_lab_bridge_v12",
                 lambda: decide_lab_bridge_v12(kappa_eff=0.5)),
        safe_run("loventre_lab_entrypoint_v12.run_lab_entrypoint_v12",
                 lambda: run_lab_entrypoint_v12(kappa_eff=0.5)),
        safe_run("loventre_lab_export_v12.run_lab_export_v12",
                 lambda: run_lab_export_v12()),
    ]

    ok = sum(results)
    fail = len(results) - ok
    print("\n===== RISULTATI LAB V12 =====")
    print(f"SUCCESSI : {ok}")
    print(f"FALLIMENTI : {fail}")
    if fail == 0:
        print("STATO : ✔ ALL GREEN (LAB sandbox pulito)")
    else:
        print("STATO : ⚠ CHECK NEEDED")

    print("\n===== END LAB V12 MINI SUITE =====\n")


if __name__ == "__main__":
    run_suite()

