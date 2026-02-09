#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
loventre_lab_decision_v12.py
------------------------------------------------
Decision layer sperimentale V12 LAB.

Pipeline:
   metrics → potential → bus → policy
Decision finale:
   SAFE
   SAFE_ACCESSIBLE
   BLACKHOLE
   WAIT

Non modifica il core.
"""

from loventre_lab_metrics_v12 import compute_lab_metrics_v12
from loventre_lab_potential_v12 import compute_lab_potential_v12
from loventre_lab_bus_v12 import run_lab_bus_v12
from loventre_lab_policy_v12 import suggest_lab_policy_v12


def run_lab_decision_v12(kappa_eff=None, entropy_eff=None):
    """
    Esegue l'intera pipeline locale V12 e sintetizza
    una decisione finale sperimentale.
    """

    # 1) metriche e potenziale
    metrics = compute_lab_metrics_v12(kappa_eff=kappa_eff,
                                      entropy_eff=entropy_eff)
    potential = compute_lab_potential_v12(kappa_eff=kappa_eff,
                                          entropy_eff=entropy_eff)

    # 2) bus state (classe V12 provvisoria)
    bus = run_lab_bus_v12(kappa_eff=kappa_eff,
                          entropy_eff=entropy_eff)

    # 3) policy V12
    hint = suggest_lab_policy_v12(
        kappa_eff=kappa_eff,
        entropy_eff=entropy_eff
    )

    # 4) deduzione decisione
    bus_state = bus["bus_state"]
    if bus_state == "BLACKHOLE-ish":
        decision = "BLACKHOLE"
    elif bus_state == "P_ACC-ish":
        decision = "SAFE_ACCESSIBLE"
    elif bus_state == "SAFE-ish":
        decision = "SAFE"
    else:
        decision = "WAIT"

    merged = {
        **metrics,
        **potential,
        **bus,
        **hint,
        "meta_label_v12": "LAB_v12_decision",
        "decision_v12": decision,
    }

    return merged


def demo():
    print("=== DEMO V12 LAB DECISION ===")
    for k in [3.0, 1.0, 0.2, -0.2, -1.0, None]:
        res = run_lab_decision_v12(kappa_eff=k, entropy_eff=None)
        print(f"kappa={str(k):>4} → {res['decision_v12']:>16} | bus={res['bus_state']:>14}")


if __name__ == "__main__":
    demo()

