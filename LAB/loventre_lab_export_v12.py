#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
loventre_lab_export_v12.py (FINAL LAB ONLY)
------------------------------------------
Esporta snapshot V12 LAB in JSON DEMO:
    • SAFE_ACCESSIBLE
    • SAFE
    • BLACKHOLE
Non influenza JSON canonici.
"""

import json
import os
from LAB.loventre_lab_entrypoint_v12 import run_lab_entrypoint_v12

OUT_DIR = "LAB_JSON_V12_DEMO"


def run_lab_export_v12():
    os.makedirs(OUT_DIR, exist_ok=True)

    cases = [
        ("lab_v12_case_safe_accessible.json", 3.0, None),
        ("lab_v12_case_safe.json", 1.0, None),
        ("lab_v12_case_blackhole.json", -1.5, None),
    ]

    for fname, kappa, entropy in cases:
        snap = run_lab_entrypoint_v12(kappa_eff=kappa,
                                      entropy_eff=entropy)
        path = os.path.join(OUT_DIR, fname)
        with open(path, "w") as f:
            json.dump(snap, f, indent=2)
        print(f"✔ scritto {path}")

    print("\n===== EXPORT LAB V12 COMPLETATO =====")
    print(f"Cartella: {OUT_DIR}")


def demo():
    print("=== DEMO LAB V12 EXPORT ===")
    run_lab_export_v12()


if __name__ == "__main__":
    demo()

