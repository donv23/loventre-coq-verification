#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
loventre_bus_l2_v12.py
----------------------
BUS layer L2 sperimentale.

Interpreta metriche L1 e produce una classe di bus semplice:
- SAFE-ish
- P_ACC-ish (se kappa_l1 > 0.8)
- BLACKHOLE-ish
- UNDEFINED-ish

Nessuna dipendenza dal LAB.
"""

from L0_CORE.loventre_labels_core_v12 import (
    SAFE,
    SAFE_ACCESSIBLE,
    BLACKHOLE,
    WAIT,
    SAFE_ISH,
    P_ACC_ISH,
    BLACKHOLE_ISH,
    UNDEFINED_ISH,
)

def run_bus_l2_v12(l1_dict):
    """
    Input:
      l1_dict (dict): deve contenere almeno:
         - kappa_l1
         - status (SAFE/BLACKHOLE/WAIT)

    Output:
      dict {
         bus_state,
         meta_label_v12
      }
    """
    if not isinstance(l1_dict, dict):
        return {"bus_state": UNDEFINED_ISH, "meta_label_v12": "L2_BUS_v12"}

    kappa = l1_dict.get("kappa_l1", None)
    status = l1_dict.get("status", None)

    # WAIT rimane UNDEFINED-ish
    if status == WAIT:
        bus = UNDEFINED_ISH

    # BLACKHOLE
    elif status == BLACKHOLE:
        bus = BLACKHOLE_ISH

    # SAFE → tenta accessibilità
    elif status == SAFE:
        if kappa is None:
            bus = SAFE_ISH
        elif kappa > 0.8:
            bus = P_ACC_ISH
        else:
            bus = SAFE_ISH
    else:
        bus = UNDEFINED_ISH

    return {
        "bus_state": bus,
        "meta_label_v12": "L2_BUS_v12"
    }


def demo():
    print("=== DEMO L2 BUS V12 ===")
    tests = [
        {"kappa_l1": None, "status": WAIT},
        {"kappa_l1": -0.5, "status": BLACKHOLE},
        {"kappa_l1": 0.1, "status": SAFE},
        {"kappa_l1": 0.9, "status": SAFE},
    ]
    for t in tests:
        out = run_bus_l2_v12(t)
        print(f"input={t} → bus={out['bus_state']}")

if __name__ == "__main__":
    demo()

