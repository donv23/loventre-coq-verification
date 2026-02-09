#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
loventre_lab_bus_v12.py  (L2 aligned FINAL)
-------------------------------------------
Classifica kappa_l1 in:
  SAFE-ish
  P_ACC-ish
  BLACKHOLE-ish
  UNDEFINED-ish
"""

from L0_CORE.loventre_labels_core_v12 import (
    SAFE_ISH,
    P_ACC_ISH,
    BLACKHOLE_ISH,
    UNDEFINED_ISH,
)


def run_lab_bus_v12(kappa_eff=None, entropy_eff=None):
    """
    Produzione di etichetta provvisoria L2.
    """
    k = kappa_eff

    if k is None:
        bus = UNDEFINED_ISH
    elif k < 0.1:
        bus = BLACKHOLE_ISH
    elif k < 0.7:
        bus = SAFE_ISH
    else:
        bus = P_ACC_ISH

    return {
        "bus_state": bus
    }


def demo():
    print("=== DEMO V12 LAB BUS (L1 aligned FINAL) ===")
    tests = [None, -0.5, 0.1, 0.65, 0.9]
    for t in tests:
        print(f"kappa_l1={t} → {run_lab_bus_v12(t)}")


if __name__ == "__main__":
    demo()

