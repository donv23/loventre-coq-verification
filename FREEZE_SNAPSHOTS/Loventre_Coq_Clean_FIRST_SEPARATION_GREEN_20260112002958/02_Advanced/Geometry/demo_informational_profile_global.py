#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Loventre Informational Potential — v5.1
Demo aggregata (lettura JSON dal motore Python)
"""

import json
import os
from loventre_informational_tools import informational_print_table

ENGINE_ROOT = os.path.join(
    "/Users",
    "vincenzoloventre",
    "Library",
    "Mobile Documents",
    "com~apple~CloudDocs",
    "ALGORITIMIA",
    "LOVENTRE_ENGINE_CLEAN",
    "loventre_engine_clean_seed"
)

JSON_LIST = [
    "metrics_seed11_cli_demo.json",
    "metrics_seed_grid_demo_global.json",
    "metrics_TSPcrit28_cli_demo.json",
    "metrics_SATcrit16_cli_demo.json",
    "metrics_2SAT_easy_demo.json",
    "metrics_2SAT_crit_demo.json"
]

def load_json_from_engine(fname):
    path = os.path.join(ENGINE_ROOT, "witness_json", fname)
    try:
        with open(path, "r") as f:
            return json.load(f)
    except Exception as e:
        print(f"[ERRORE] Non posso leggere {path}: {e}")
        return None

def main():
    rows = []
    for fname in JSON_LIST:
        M = load_json_from_engine(fname)
        if M is None:
            continue

        rows.append([
            fname,
            M.get("kappa_eff", None),
            M.get("entropy_eff", None),
            M.get("V0", None),
            M.get("informational_potential", None),
            M.get("p_tunnel", None),
            M.get("P_success", None),
            M.get("risk_class", None),
            M.get("meta_label", None),
        ])

    print("")
    print("==============================================================")
    print(" LOVENTRE – V5.1 Informational Potential (Seed Showcase)")
    print("==============================================================")
    print("")
    print("===============================================")
    print("=== LOVENTRE INFORMATIONAL POTENTIAL TABLE ===")
    print("===============================================")
    print("")

    headers = [
        "json",
        "kappa",
        "entropy",
        "V0",
        "info_P",
        "p_tunnel",
        "P_success",
        "risk",
        "meta"
    ]

    informational_print_table(headers, rows)
    print("")
    print("DONE.")
    print("")

if __name__ == "__main__":
    main()

