#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
import json

from loventre_informational_tools import (
    informational_potential,
    informational_inertia,
    informational_print_table
)

WITNESS_DIR = os.path.abspath(
    "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed/witness_json"
)

FILES = [
    "m_seed11_cli_demo.json",
    "m_seed_grid_demo.json",
    "m_TSPcrit28_cli_demo.json",
    "m_SATcrit16_cli_demo.json",
    "m_2SAT_easy_demo.json",
    "m_2SAT_crit_demo.json"
]


def classify_and_suggest(k, H, V0):
    """
    Ritorna: class, phase, gravity, suggestion
    """
    if k is None or H is None or V0 is None:
        return "UNKNOWN", "UNDEF", "N/A", "INSUFFICIENT_DATA"

    P = informational_potential(k, H, V0)
    I = informational_inertia(k, H, V0)

    if P is None or I is None:
        return "UNKNOWN", "UNDEF", "N/A", "INSUFFICIENT_DATA"

    # gravità informazionale
    gravity = round(abs(P - I), 3)

    # semantica minima coerente e fisica:
    if gravity < 0.20:
        return "SAFE", "FLAT", gravity, "INSISTI"
    elif gravity < 0.35:
        return "ACCESSIBLE", "EASY", gravity, "VALUTA"
    else:
        return "BLACK_HOLE", "SCHWARZSCHILD", gravity, "RITIRA"


def load_vals(fname):
    try:
        full = os.path.join(WITNESS_DIR, fname)
        with open(full,"r") as f:
            obj = json.load(f)
        k = obj.get("kappa_eff")
        e = obj.get("entropy_eff")
        v = obj.get("V0")
        return k,e,v
    except Exception as ex:
        return None,None,None


print("\n=================================================================")
print(" LOVENTRE POLICY SUGGESTION V5.3-TER (Enhanced View Stable)")
print("=================================================================\n")

rows = []
for f in FILES:
    k, H, v0 = load_vals(f)
    cls, ph, grav, sugg = classify_and_suggest(k, H, v0)
    rows.append([f, cls, ph, grav, sugg])

headers = ["json", "class", "phase", "gravity", "suggestion"]
informational_print_table(headers, rows)

print("\n=================================================================\n")

