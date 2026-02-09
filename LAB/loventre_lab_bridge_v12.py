#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
loventre_lab_bridge_v12.py (L1–L2–L3 aligned FINAL)
--------------------------------------------------
Collega Decisione LAB con il Bridge CORE.
"""

import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.append(ROOT)

from L0_CORE.loventre_bridge_core_v12 import pack_bridge_v12
from LAB.loventre_lab_decision_v12 import run_lab_decision_v12


def decide_lab_bridge_v12(kappa_eff=None, entropy_eff=None):
    """
    Aggiunge colore/score dal CORE al risultato LAB.
    """
    dec = run_lab_decision_v12(kappa_eff=kappa_eff,
                               entropy_eff=entropy_eff)

    out = pack_bridge_v12(
        bridge_decision_v12=dec["decision_v12"],
        bus_state=dec["bus_state"]
    )

    return {
        **dec,
        **out,
        "meta_label_v12": "LAB_v12_bridge",
    }


def demo():
    print("=== DEMO V12 LAB BRIDGE (FULL) ===")
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
        print(f"kappa={str(k):>4}, ent={str(e):>4} → "
              f"{out['decision_v12']:>16} | "
              f"color={out['bridge_color_v12']:>6} | "
              f"score={out['bridge_score_v12']:.1f}")


if __name__ == "__main__":
    demo()

