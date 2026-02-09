#!/usr/bin/env python3
# ============================================================
# LOVENTRE — FAMILY PRE-CRITICAL COMPARISON
# ============================================================
# - Confronto osservativo tra famiglie di problemi
# - Nessun effetto decisionale
# - Usa Pre-Critical Observer + meta_label
# ============================================================

import json
from typing import List, Dict, Any

from loventre_precritical_observer import analyze_precritical


def load_sequence(path: str) -> List[Dict[str, Any]]:
    with open(path, "r", encoding="utf-8") as f:
        data = json.load(f)
    if not isinstance(data, list):
        raise ValueError("Il file deve contenere una lista di metrics.")
    return data


def analyze_family(name: str, sequence: List[Dict[str, Any]]) -> None:
    print(f"\n=== FAMILY: {name} ===")

    prev = None
    for i, curr in enumerate(sequence):
        print(f"\n--- STEP {i} ---")
        print(f"meta_label      : {curr.get('meta_label')}")
        print(f"horizon_flag    : {curr.get('horizon_flag')}")

        if prev is not None:
            report = analyze_precritical(prev, curr)
            print(f"pre_critical    : {report['pre_critical_flag']}")
            print(f"signals         : {report['pre_critical_signals']}")
        else:
            print("pre_critical    : (n/a)")

        prev = curr


def main():
    families = {
        "2-SAT": "family_sequences/2sat_sequence.json",
        "3-SAT": "family_sequences/3sat_sequence.json",
        "TSP":   "family_sequences/tsp_sequence.json",
    }

    for name, path in families.items():
        try:
            seq = load_sequence(path)
            analyze_family(name, seq)
        except FileNotFoundError:
            print(f"\n[SKIP] {name}: file non trovato ({path})")


if __name__ == "__main__":
    main()

