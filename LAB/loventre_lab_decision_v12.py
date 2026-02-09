#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
loventre_lab_decision_v12.py (FINAL)
------------------------------------------------
Pipeline sperimentale V12:
   L1 metrics → potential → bus → policy → decision
"""

from L1_METRICS.loventre_metrics_l1_v12 import compute_l1_metrics_v12
from LAB.loventre_lab_potential_v12 import compute_lab_potential_v12
from LAB.loventre_lab_bus_v12 import run_lab_bus_v12
from LAB.loventre_lab_policy_v12 import suggest_lab_policy_v12


def run_lab_decision_v12(kappa_eff=None, entropy_eff=None):
    """
    Esegue l'intera pipeline locale V12 e sintetizza
    una decisione finale sperimentale.
    """

    l1 = compute_l1_metrics_v12(raw_value=kappa_eff)

    potential = compute_lab_potential_v12(
        kappa_eff=l1["kappa_l1"],
        entropy_eff=entropy_eff
    )

    bus = run_lab_bus_v12(
        kappa_eff=l1["kappa_l1"],
        entropy_eff=entropy_eff
    )

    hint = suggest_lab_policy_v12(
        kappa_eff=l1["kappa_l1"],
        entropy_eff=entropy_eff
    )

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
        **l1,
        **potential,
        **bus,
        **hint,
        "meta_label_v12": "LAB_v12_decision",
        "decision_v12": decision,
    }

    return merged


def demo():
    print("=== DEMO V12 LAB DECISION (L1-aligned FINAL) ===")
    for k in [3.0, 1.0, 0.2, -0.2, -1.0, None]:
        out = run_lab_decision_v12(kappa_eff=k, entropy_eff=None)
        print(f"kappa={str(k):>4} → {out['decision_v12']:>16} | bus={out['bus_state']:>14}")


if __name__ == "__main__":
    demo()

