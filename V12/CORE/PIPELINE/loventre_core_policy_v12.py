#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
loventre_core_policy_v12.py
--------------------------------------
CORE POLICY V12 – sandbox avanzata.

Legge lo snapshot dal CORE BUS
e aggiunge una decisione sintetica:

  P_ACC-ish      →  policy: expand_and_explore
  SAFE-ish       →  policy: maintain_stability
  BLACKHOLE-ish  →  policy: halt
  UNDEFINED      →  policy: noop

Nessun JSON, nessun LAB, nessuna scrittura su disco.
"""

import os
import sys

HERE = os.path.abspath(os.path.dirname(__file__))        # .../V12/CORE/PIPELINE
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))   # .../V12
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))

for p in (ROOT, REPO):
    if p not in sys.path:
        sys.path.append(p)

from V12.CORE.PIPELINE.loventre_core_bus_v12 import compute_core_bus_v12


def compute_core_policy_v12(kappa_eff=None, entropy_eff=None):
    """
    Applica una decisione di policy minimale alla classificazione del bus.
    """
    snap = compute_core_bus_v12(kappa_eff=kappa_eff,
                                entropy_eff=entropy_eff)

    state = snap.get("bus_state_core")

    if state == "P_ACC-ish":
        hint = "expand_and_explore"
    elif state == "SAFE-ish":
        hint = "maintain_stability"
    elif state == "BLACKHOLE-ish":
        hint = "halt"
    else:
        hint = "noop"

    return {
        **snap,
        "meta_label_v12": "CORE_v12_policy",
        "policy_core_v12": hint
    }


def smoke_test():
    print("=== CORE POLICY V12 ===")
    for k in (2.0, 0.8, -1.2, None):
        print(k, "→", compute_core_policy_v12(k, 4.0 if k else None))


if __name__ == "__main__":
    smoke_test()

