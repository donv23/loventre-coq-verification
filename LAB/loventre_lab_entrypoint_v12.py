#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
loventre_lab_entrypoint_v12.py (FINAL L1–L2–L3–CORE)
----------------------------------------------------
Esegue:
  1) decisione V12 L1–L2–L3
  2) bridge colore+score dal CORE
  3) ritorna snapshot integrato
"""

from LAB.loventre_lab_decision_v12 import run_lab_decision_v12
from LAB.loventre_lab_bridge_v12 import decide_lab_bridge_v12


def run_lab_entrypoint_v12(kappa_eff=None, entropy_eff=None):
    """
    Snapshot integrato V12:
      Metrics → Potential → Bus → Policy → Decision + Bridge CORE
    """
    dec = run_lab_decision_v12(kappa_eff=kappa_eff,
                               entropy_eff=entropy_eff)

    br = decide_lab_bridge_v12(
        kappa_eff=kappa_eff,
        entropy_eff=entropy_eff
    )

    merged = {
        **dec,
        **br,
        "meta_label_v12": "LAB_v12_entrypoint_FULL",
    }
    return merged


def demo():
    print("=== DEMO V12 LAB ENTRYPOINT (FINAL L1–L2–L3–CORE) ===\n")
    for k in [3.0, 1.0, 0.2, -0.2, -1.0, None]:
        out = run_lab_entrypoint_v12(kappa_eff=k, entropy_eff=None)
        print(f"kappa={str(k):>4} → dec={out['decision_v12']:>16} | "
              f"bridge={out['bridge_decision_v12']:>16} | "
              f"color={out['bridge_color_v12']:>6}")


if __name__ == "__main__":
    demo()

