"""
Axis F — Conditional Bridge Hypothesis (LAB)

Author: Vincenzo Loventre
Status: LAB / NON-CANONICAL
Purpose:
    Explore a conditional correspondence between the Loventre structural model
    and classical complexity notions (P vs NP), WITHOUT modifying the frozen engine.

IMPORTANT:
    - This file reads existing witness JSON only.
    - It introduces NO new metrics.
    - It performs NO inference on the engine.
    - All conclusions are CONDITIONAL and NON-CLAIMING.

Canonical safety:
    The Loventre Engine and Coq Canon are NOT affected by this file.
"""

import json
import os
from typing import Dict, Any, List


# ------------------------------------------------------------
# Configuration (READ-ONLY)
# ------------------------------------------------------------

WITNESS_DIR = os.path.join("..", "witness_json")

CLASSICAL_FAMILIES = {
    "2SAT": "P-like (classical)",
    "SAT": "NP-complete (classical)",
    "3SAT": "NP-complete (classical)",
    "TSP": "NP-complete (classical)",
}


# ------------------------------------------------------------
# Utilities
# ------------------------------------------------------------

def load_json(path: str) -> Dict[str, Any]:
    with open(path, "r") as f:
        return json.load(f)


def list_witness_files() -> List[str]:
    if not os.path.isdir(WITNESS_DIR):
        raise RuntimeError(f"Witness directory not found: {WITNESS_DIR}")
    return [
        f for f in os.listdir(WITNESS_DIR)
        if f.endswith(".json")
    ]


# ------------------------------------------------------------
# Axis F core logic (pure inspection)
# ------------------------------------------------------------

def classify_witness(filename: str, data: Dict[str, Any]) -> Dict[str, Any]:
    name = filename.lower()

    classical_hint = None
    for key in CLASSICAL_FAMILIES:
        if key.lower() in name:
            classical_hint = CLASSICAL_FAMILIES[key]
            break

    structural_regime = data.get("meta_label") or data.get("global_decision")

    return {
        "file": filename,
        "classical_hint": classical_hint,
        "structural_regime": structural_regime,
        "comment": (
            "No claim made. Alignment is conditional."
            if classical_hint else
            "No classical mapping attempted."
        )
    }


def run_axis_f_analysis() -> List[Dict[str, Any]]:
    results = []
    for fname in list_witness_files():
        path = os.path.join(WITNESS_DIR, fname)
        data = load_json(path)
        results.append(classify_witness(fname, data))
    return results


# ------------------------------------------------------------
# Entry point (LAB execution only)
# ------------------------------------------------------------

if __name__ == "__main__":
    print("Axis F — Conditional Analysis (LAB)")
    print("Reading witness JSON from:", WITNESS_DIR)
    print("-" * 60)

    results = run_axis_f_analysis()
    for r in results:
        print(json.dumps(r, indent=2))

    print("-" * 60)
    print("END — No claims. No engine modification.")

