#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
loventre_lab_bridge_v12.py
----------------------------------------
Mini bridge V12 sperimentale

Pipeline locale (non canonica):
    metrics → potential → bus → policy → decision_v12 → bridge return

Output sintetico:
    decision_v12 (SAFE, SAFE_ACCESSIBLE, BLACKHOLE, WAIT)
    color      (GREEN/YELLOW/RED)
    score      (0.0–1.0 grezzo)
    raw_merge  (dettagli interni, opzionale)
"""

from loventre_lab_decision_v12 import run_lab_decision_v12


def decide_lab_bridge_v12(kappa_eff=None, entropy_eff=None):
    """
    Converte la decisione locale V12 in un output da bridge.
    Il formato è volutamente leggero e sperimentale.
    """

    dec = run_lab_decision_v12(
        kappa_eff=kappa_eff,
        entropy_eff=entropy_eff,
    )

    # Estrarre la decisione da V12
    decision = dec.get("decision_v12", "WAIT")

    # Mapping molto semplice
    if decision == "SAFE_ACCESSIBLE":
        color = "GREEN"
        score = 1.0
    elif decision == "SAFE":
        color = "GREEN"
        score = 0.8
    elif decision == "BLACKHOLE":
        color = "RED"
        score = 0.0
    else:  # WAIT o qualsiasi altro
        color = "YELLOW"
        score = 0.5

    return {
        "bridge_decision_v12": decision,
        "bridge_color_v12": color,
        "bridge_score_v12": score,
        "meta_label_v12": "LAB_v12_bridge",
    }


def demo():
    print("=== DEMO V12 LAB BRIDGE ===")
    tests = [
        (3.0, None),
        (1.0, None),
        (0.2, None),
        (-0.4, None),
        (-2.0, None),
        (None, 5.0),
    ]
    for k, e in tests:
        out = decide_lab_bridge_v12(kappa_eff=k, entropy_eff=e)
        print(f"kappa={k}, ent={e} → {out['bridge_decision_v12']:>16} | color={out['bridge_color_v12']:>6} | score={out['bridge_score_v12']}")


if __name__ == "__main__":
    demo()

