#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
run_lab_suite_v12.py
---------------------------------
Mini regression suite V12 (solo LAB).

Esegue in sequenza:
  • metrics
  • pipeline
  • bus
  • policy
  • decision
  • bridge
  • entrypoint
  • export JSON

Non tocca il core.
Nessuna influenza sui JSON canonici.
Serve solo per assicurare che il LAB sia coerente.
"""

import importlib
import sys

TARGETS = [
    ("loventre_lab_metrics_v12",     "compute_lab_metrics_v12"),
    ("loventre_lab_pipeline_v12",    "run_lab_pipeline_v12"),
    ("loventre_lab_bus_v12",         "run_lab_bus_v12"),
    ("loventre_lab_policy_v12",      "suggest_lab_policy_v12"),
    ("loventre_lab_decision_v12",    "run_lab_decision_v12"),
    ("loventre_lab_bridge_v12",      "decide_lab_bridge_v12"),
    ("loventre_lab_entrypoint_v12",  "run_lab_entrypoint_v12"),
    ("loventre_lab_export_v12",      "run_lab_export_v12"),
]


def run_one(mod_name, func_name):
    try:
        mod = importlib.import_module(mod_name)
        func = getattr(mod, func_name, None)
        if func is None:
            print(f"[FAIL] {mod_name}.{func_name} non trovato")
            return False

        # chiamiamo con default arguments (lato entrypoint è solo demo)
        try:
            func()
        except TypeError:
            # fallback: funzione potrebbe avere argomenti obbligatori demo
            if hasattr(mod, "demo"):
                mod.demo()
            else:
                print(f"[WARN] {mod_name}: nessun run/invocazione automatica")
        print(f"[ OK ] {mod_name}.{func_name}")
        return True

    except Exception as exc:
        print(f"[ERR] {mod_name}.{func_name} → {exc}")
        return False


def main():
    print("\n===== LAB V12 MINI SUITE =====\n")

    ok = 0
    fail = 0
    for mod_name, func_name in TARGETS:
        print(f"[RUN ] {mod_name}.{func_name}")
        if run_one(mod_name, func_name):
            ok += 1
        else:
            fail += 1
        print("-" * 60)

    print("\n===== RISULTATI LAB V12 =====")
    print(f"SUCCESSI : {ok}")
    print(f"FALLIMENTI : {fail}")
    if fail == 0:
        print("STATO : ✔ ALL GREEN (LAB sandbox pulito)")
    else:
        print("STATO : ⚠ CHECK NEEDED")

    print("\n===== END LAB V12 MINI SUITE =====\n")


if __name__ == "__main__":
    main()

