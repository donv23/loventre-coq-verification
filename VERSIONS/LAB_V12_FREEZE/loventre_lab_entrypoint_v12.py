#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
loventre_lab_entrypoint_v12.py
------------------------------------
Entry point V12 minimo.
Chiama:
  • decision
  • bridge
  • stampa finale
Non tocca il core e non produce JSON canonici.
"""

from loventre_lab_decision_v12 import run_lab_decision_v12
from loventre_lab_bridge_v12 import decide_lab_bridge_v12


def run_lab_entrypoint_v12(kappa_eff=None, entropy_eff=None):
    """
    Singolo snapshot V12: decisione + bridge.
    """
    dec = run_lab_decision_v12(kappa_eff=kappa_eff,
                               entropy_eff=entropy_eff)

    br = decide_lab_bridge_v12(kappa_eff=kappa_eff,
                               entropy_eff=entropy_eff)

    merged = {
        **dec,
        **br,
        "meta_label_v12": "LAB_v12_entrypoint",
    }

    return merged


def demo():
    print("=== DEMO V12 LAB ENTRYPOINT ===\n")
    print("No entropy:")
    for k in [3.0, 1.0, 0.2, -0.2, -1.0, -2.5]:
        out = run_lab_entrypoint_v12(kappa_eff=k, entropy_eff=None)
        print(f"kappa={k:4} → {out['decision_v12']:>16} | color={out['bridge_color']:>6} | score={out['bridge_score']:.1f}")

    print("\nWith entropy:")
    tests = [(3.0, 1.0), (1.0, 4.0), (-0.7, 2.0), (None, 5.0)]
    for k, e in tests:
        out = run_lab_entrypoint_v12(kappa_eff=k, entropy_eff=e)
        print(f"kappa={str(k):>4}, ent={str(e):>4} → {out['decision_v12']:>16} | color={out['bridge_color']:>6} | score={out['bridge_score']:.1f}")


if __name__ == "__main__":
    demo()

