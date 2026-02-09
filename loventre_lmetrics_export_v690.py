import json
from pathlib import Path
import sys

# Dummy canonical values for v690 evolution chain
# (replace later with engine-computed values)

profiles = {
    "P_like": {
        "kappa_eff": 0.12,
        "entropy_eff": 0.18,
        "V0": 0.05,
        "p_tunnel": 0.82,
        "P_success": 0.92,
        "gamma_dilation": 0.02,
        "time_regime": 0,
        "risk_index": 0.10
    },
    "Pacc": {
        "kappa_eff": 0.34,
        "entropy_eff": 0.46,
        "V0": 0.22,
        "p_tunnel": 0.40,
        "P_success": 0.57,
        "gamma_dilation": 0.11,
        "time_regime": 1,
        "risk_index": 0.42
    },
    "Crit": {
        "kappa_eff": 0.71,
        "entropy_eff": 0.80,
        "V0": 0.66,
        "p_tunnel": 0.07,
        "P_success": 0.17,
        "gamma_dilation": 0.28,
        "time_regime": 2,
        "risk_index": 0.87
    }
}

def write_json(name, data):
    out = Path(name)
    out.write_text(json.dumps(data, indent=2))
    print(f"Wrote {out}")

if __name__ == "__main__":
    base = Path("/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/JSON_IO")

    write_json(base / "metrics_P_like_v690.json", profiles["P_like"])
    write_json(base / "metrics_Pacc_v690.json", profiles["Pacc"])
    write_json(base / "metrics_3SATcrit_v690.json", profiles["Crit"])

