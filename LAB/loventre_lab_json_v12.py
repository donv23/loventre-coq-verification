#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
loventre_lab_json_v12.py
--------------------------------------
Writer LAB V12 completamente sandbox.

• Importa il top dello stack LAB (policy)
• Valuta 3 casi: SAFE, BH, NONE-case
• Esporta JSON in LAB/JSON/
• Nessuna interferenza con JSON_IO canonico
• Totalmente opzionale e cancellabile
"""

import json
import os
from loventre_lab_policy_v12 import run_lab_policy_v12

def ensure_dir(path):
    if not os.path.exists(path):
        os.makedirs(path, exist_ok=True)

def write_json(snapshot, filename):
    ensure_dir("LAB/JSON")
    fullpath = os.path.join("LAB/JSON", filename)
    with open(fullpath, "w") as f:
        json.dump(snapshot, f, indent=2)
    return fullpath

def run_and_write_all():
    results = {}

    safeish = run_lab_policy_v12(2.0, 4.0)
    results["safeish"] = write_json(safeish, "lab_v12_safeish.json")

    bhish = run_lab_policy_v12(-1.2, None)
    results["bhish"] = write_json(bhish, "lab_v12_bhish.json")

    nonecase = run_lab_policy_v12()
    results["none"] = write_json(nonecase, "lab_v12_none.json")

    return results

def demo():
    print("=== V12 LAB JSON WRITER ===")
    outpaths = run_and_write_all()
    for k, p in outpaths.items():
        print(f"[{k}] -> {p}")

if __name__ == "__main__":
    demo()

