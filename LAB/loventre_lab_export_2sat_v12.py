#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
loventre_lab_export_2sat_v12.py
------------------------------------
Export JSON semplice dei 3 profili 2-SAT V12 nel LAB.

• EASY      → P_ACC-ish
• CRITICAL  → SAFE-ish
• HARD      → BLACKHOLE-ish

Nessuna influenza sul core.
Salva in LAB_JSON_2SAT_V12/
"""

import json
import os

from loventre_lab_2sat_profiles_v12 import (
    run_lab_2sat_easy_profile_v12,
    run_lab_2sat_crit_profile_v12,
    run_lab_2sat_hard_profile_v12,
)


def run_lab_export_2sat_v12():
    """
    Export dei tre profili 2-SAT LAB.
    """
    out_dir = "LAB_JSON_2SAT_V12"
    os.makedirs(out_dir, exist_ok=True)

    cases = [
        ("easy",  run_lab_2sat_easy_profile_v12()),
        ("crit",  run_lab_2sat_crit_profile_v12()),
        ("hard",  run_lab_2sat_hard_profile_v12()),
    ]

    print("=== DEMO LAB V12 2-SAT EXPORT ===")
    for label, data in cases:
        fname = f"{out_dir}/lab_v12_2sat_{label}.json"
        with open(fname, "w") as f:
            json.dump(data, f, indent=4)
        print(f"✔ scritto {fname}")

    print("\n===== EXPORT LAB V12 2-SAT COMPLETATO =====")
    print(f"Cartella: {out_dir}")


def demo():
    run_lab_export_2sat_v12()


if __name__ == "__main__":
    demo()

