#!/usr/bin/env python3
"""
loventre_lmetrics_export_v31.py

Export canonico LMetrics → JSON per Coq v3+
Regole:
- formati invariabili
- nessun campo opzionale
- default espliciti
- directory di output fissa JSON_IO/LMetrics_v3_for_Coq/
"""

import json
import os
from pathlib import Path
from typing import Dict, Any

# ======================================================================
# CONFIG CANONICO
# ======================================================================

LMETRICS_KEYS = [
    "kappa_eff",
    "entropy_eff",
    "V0",
    "a_min",
    "p_tunnel",
    "P_success",
    "gamma_dilation",
    "time_regime",
    "mass_eff",
    "inertial_idx",
    "risk_index",
    "risk_class",
    "chi_compactness",
    "horizon_flag",
    "flag_P",
    "flag_P_acc",
    "flag_NP_bh"
]

DEFAULTS = {
    "kappa_eff": 0.0,
    "entropy_eff": 0.0,
    "V0": 0.0,
    "a_min": 0.0,
    "p_tunnel": 0.0,
    "P_success": 0.0,
    "gamma_dilation": 0.0,
    "time_regime": "unknown",
    "mass_eff": 0.0,
    "inertial_idx": 0.0,
    "risk_index": 0.0,
    "risk_class": "unknown",
    "chi_compactness": 0.0,
    "horizon_flag": False,
    "flag_P": False,
    "flag_P_acc": False,
    "flag_NP_bh": False
}

INPUT_DIR = Path("metrics")
OUTPUT_DIR = Path("JSON_IO") / "LMetrics_v3_for_Coq"
OUTPUT_DIR.mkdir(parents=True, exist_ok=True)

# ======================================================================
# CORE FUNZIONI
# ======================================================================

def load_metrics_file(path: Path) -> Dict[str, Any]:
    """Leggi JSON, ritorna dict."""
    with open(path, "r") as f:
        return json.load(f)

def normalize_entry(raw: Dict[str, Any]) -> Dict[str, Any]:
    """
    Garantisce che il dict finale rispetti lo schema canonico.
    Campi mancanti → default.
    """
    result = {}
    for key in LMETRICS_KEYS:
        result[key] = raw.get(key, DEFAULTS[key])
    return result

def export_one(name: str, src: str):
    src_path = INPUT_DIR / src
    if not src_path.exists():
        print(f"[WARN] File metrics assente: {src_path}")
        return
    raw = load_metrics_file(src_path)
    norm = normalize_entry(raw)
    dst_path = OUTPUT_DIR / f"{name}.json"
    with open(dst_path, "w") as f:
        json.dump(norm, f, indent=2, sort_keys=True)
    print(f"[OK] Esportato: {dst_path}")

def main():
    # Canonico GRID
    export_one("lmetrics_seed_grid_demo", "metrics_seed_grid_demo_global.json")

    # Canonico 2SAT easy
    export_one("lmetrics_2sat_easy_demo", "metrics_2SAT_easy_demo.json")

    # Canonico 2SAT crit
    export_one("lmetrics_2sat_crit_demo", "metrics_2SAT_crit_demo.json")

    print("\n=== EXPORT V31 COMPLETATO ===")
    print(f"Output in: {OUTPUT_DIR}")

if __name__ == "__main__":
    main()

