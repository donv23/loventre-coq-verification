#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
loventre_lab_demo_all_v12.py
----------------------------------------
Mostra l'intero stack LAB V12 in azione:

metrics → potential → pipeline → bus → policy → bridge

Nessun write, nessun core, sandbox totale.
"""

from loventre_lab_metrics_v12 import compute_lab_metrics_v12
from loventre_lab_potential_v12 import compute_lab_potential_v12
from loventre_lab_pipeline_v12 import run_lab_pipeline_v12
from loventre_lab_bus_v12 import build_lab_bus_v12
from loventre_lab_policy_v12 import run_lab_policy_v12
from loventre_lab_bridge_v12 import bridge_case


def demo_all(case_label, kappa_eff=None, entropy_eff=None):
    print(f"\n=== CASE: {case_label} ===")

    m = compute_lab_metrics_v12(kappa_eff, entropy_eff)
    print("[METRICS]", m)

    p = compute_lab_potential_v12(kappa_eff, entropy_eff)
    print("[POTENTIAL]", p)

    pipe = run_lab_pipeline_v12(kappa_eff, entropy_eff)
    print("[PIPELINE]", pipe)

    bus = build_lab_bus_v12(kappa_eff, entropy_eff)
    print("[BUS]", bus)

    policy = run_lab_policy_v12(kappa_eff, entropy_eff)
    print("[POLICY]", policy)

    bridged = bridge_case(kappa_eff, entropy_eff)
    print("[BRIDGE JSON]\n", bridged)


def main():
    print("==== V12 LAB FULL STACK DEMO ====")

    demo_all("SAFE-ish", 2.0, 4.0)
    demo_all("BH-ish", -1.2, None)
    demo_all("NONE-case", None, None)

    print("\n==== END V12 LAB FULL STACK DEMO ====")


if __name__ == "__main__":
    main()

