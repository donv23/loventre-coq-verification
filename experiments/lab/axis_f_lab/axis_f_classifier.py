"""
Axis F — Explicit Classification (LAB ONLY)

This module introduces an explicit three-layer distinction:
- NP-classical      (external label, non-operational)
- NP-instance       (quantitative difficulty of the instance)
- NP-structural     (Loventre regime already computed)

NO claims are made.
NO engine logic is modified.
"""

import json
import os

WITNESS_DIR = "../witness_json"


def classify_np_classical(filename: str) -> str:
    name = filename.lower()
    if "2sat" in name:
        return "P"
    if "3sat" in name or "tsp" in name or "satcrit" in name:
        return "NP-complete"
    return "unknown"


def classify_instance_profile(metrics: dict) -> str:
    kappa = metrics.get("kappa_eff")
    p_tunnel = metrics.get("p_tunnel")

    if kappa is None or p_tunnel is None:
        return "unknown"

    if kappa < 0.3 and p_tunnel > 0.6:
        return "easy"
    if 0.3 <= kappa <= 0.6:
        return "critical"
    return "hard"


def classify_structural_regime(metrics: dict) -> str:
    return metrics.get("meta_label", "unknown")


def load_json(path):
    with open(path, "r") as f:
        return json.load(f)


def main():
    print("Axis F — Explicit NP Distinction (LAB)")
    print("-" * 60)

    for fname in sorted(os.listdir(WITNESS_DIR)):
        if not fname.endswith(".json"):
            continue

        path = os.path.join(WITNESS_DIR, fname)
        data = load_json(path)

        metrics = data.get("metrics", data)

        result = {
            "file": fname,
            "NP_classical": classify_np_classical(fname),
            "NP_instance_profile": classify_instance_profile(metrics),
            "NP_structural_regime": classify_structural_regime(metrics),
            "note": "Descriptive only. No claim."
        }

        print(json.dumps(result, indent=2))

    print("-" * 60)
    print("END — LAB ONLY. No engine modification.")


if __name__ == "__main__":
    main()

