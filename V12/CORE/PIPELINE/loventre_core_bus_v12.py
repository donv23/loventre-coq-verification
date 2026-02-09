#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
loventre_core_bus_v12.py
--------------------------------------
CORE BUS V12 — nessun LAB.

Combina:
 • CORE metrics
 • CORE potential
 • classificazione simbolica

Nessuna scrittura su disco.
Nessun JSON.
Preparazione per Policy CORE.
"""

import os
import sys

HERE = os.path.abspath(os.path.dirname(__file__))        # .../V12/CORE/PIPELINE
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))   # .../V12
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))

for p in (ROOT, REPO):
    if p not in sys.path:
        sys.path.append(p)

from V12.CORE.PIPELINE.loventre_core_pipeline_v12 import compute_core_pipeline_v12


def compute_core_bus_v12(kappa_eff=None, entropy_eff=None):
    """
    Costruisce il mini BUS CORE V12.
    Logica volutamente minimale:
       k > 1.5 → P_ACC-ish
       k >= 0 → SAFE-ish
       k < 0 → BLACKHOLE-ish
    """
    snap = compute_core_pipeline_v12(kappa_eff=kappa_eff,
                                     entropy_eff=entropy_eff)

    k = snap.get("kappa_eff")

    if k is None:
        state = "UNDEFINED-ish"
    elif k < 0:
        state = "BLACKHOLE-ish"
    elif k < 1.5:
        state = "SAFE-ish"
    else:
        state = "P_ACC-ish"

    return {
        **snap,
        "meta_label_v12": "CORE_v12_bus",
        "bus_state_core": state,
    }


def smoke_test():
    print("=== CORE BUS V12 ===")
    for k in (2.0, 0.8, -1.2, None):
        print(k, "→", compute_core_bus_v12(k, 4.0 if k else None))


if __name__ == "__main__":
    smoke_test()

