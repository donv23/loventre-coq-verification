#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
V13_NEXT / loventre_export_l6_v13.py
-------------------------------------------------
Esporta 3 snapshot V13 *solo sandbox*:

  • SAFE_ACCESSIBLE
  • SAFE
  • BLACKHOLE

Nessun effetto su JSON canonici legacy.
"""

import json
import os

from V13_NEXT.L5_ENTRYPOINT.loventre_entrypoint_l5_v13 import run_entrypoint_v13

OUT_DIR = "V13_JSON_DEMO"


def run_export_l6_v13():
    """
    Produce 3 file JSON sandbox V13 basati su kappa di esempio.
    """
    os.makedirs(OUT_DIR, exist_ok=True)

    cases = [
        ("v13_case_safe_accessible.json", 1.2),
        ("v13_case_safe.json", 0.3),
        ("v13_case_blackhole.json", -1.5),
    ]

    for fname, raw in cases:
        snap = run_entrypoint_v13(raw_value=raw)
        path = os.path.join(OUT_DIR, fname)
        with open(path, "w") as f:
            json.dump(snap, f, indent=2)
        print(f"✔ scritto {path}")

    print("\n===== EXPORT V13 COMPLETATO =====")
    print(f"Cartella: {OUT_DIR}")


def demo():
    print("=== DEMO EXPORT V13 ===")
    run_export_l6_v13()


if __name__ == "__main__":
    demo()

