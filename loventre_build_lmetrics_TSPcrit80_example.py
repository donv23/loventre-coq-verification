#!/usr/bin/env python3
"""
Loventre Engine V10 — build LMetrics TSPcrit80 (placeholder critico)
"""
import json
from pathlib import Path

def main():
    data = {
        "kappa_eff": -0.80,
        "entropy_eff": 3.0,
        "V0": 1.0,
        "a_min": 0.1,
        "p_tunnel": 0.20,
        "P_success": 0.2,
        "gamma_dilation": 1.5,
        "time_regime": "critical",
        "mass_eff": 1.2,
        "inertial_idx": 0.80,
        "risk_index": 0.80,
        "risk_class": "HIGH",
        "chi_compactness": 0.5,
        "horizon_flag": True,
        "global_decision_tag": "BLOCK",
        "meta_label": "meta_TSPcrit80_v10",
    }

    out = Path("JSON_IO/JSON_OUTPUT/metrics_TSPcrit80_v10.json")
    out.parent.mkdir(parents=True, exist_ok=True)
    with out.open("w") as f:
        json.dump(data, f, indent=2)

    print("[OK] metrics_TSPcrit80_v10.json scritto")

if __name__ == "__main__":
    main()

