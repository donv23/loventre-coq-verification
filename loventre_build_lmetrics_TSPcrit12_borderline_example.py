#!/usr/bin/env python3
"""
LOVENTRE ENGINE – LMetrics example for TSP_crit_12 (borderline)
===============================================================

Questo script costruisce un esempio concreto di bus LMetrics
per una istanza NP_like_critico tipo TSP_crit_12, usando i
valori qualitativi visti nelle tabelle del motore:

  n_cities  kappa_eff  entropy_eff   V0       a_min   p_tunnel(E)
       12     0.550       0.750   1.5876    2.50    5.438e-03

  P_success ≈ 9.957e-01
  gamma_dil ≈ 6.21
  mass_eff ≈ 1.925
  inert_idx ≈ 11.963
  time_regime = time_hyperbolic
  meta_label = NP_like_critico
  risk_class = NP_like_critico
  loventre_global_decision ≈ VALUTA / AMBER
  loventre_global_score ≈ 0.269

Qui fissiamo:
  - chi_compactness ≈ 0.70 (near-horizon ma non black-hole),
  - risk_index ≈ 6.0 (intermedio),
  - horizon_flag = false (ancora prima dell'orizzonte),
  - loventre_global_decision = GD_borderline,
  - loventre_global_color = GC_amber,
  - loventre_global_score = 0.269.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Dict, Any


def build_lmetrics_TSPcrit12_borderline() -> Dict[str, Any]:
    """Costruisce il dict che rappresenta m_TSPcrit12_borderline a livello LMetrics."""
    return {
        # Core geometric / energetic metrics
        "kappa_eff": 0.550,
        "entropy_eff": 0.750,
        "V0": 1.5876,
        "a_min": 2.50,

        # Tunneling and success probability
        "p_tunnel": 5.438e-03,
        "P_success": 9.957e-01,

        # Relativistic / mass-like indices
        "gamma_dilation": 6.21,
        "time_regime": "time_hyperbolic",
        "mass_eff": 1.925,
        "inertial_idx": 11.963,

        # Risk metrics (NP_like_critico, non ancora black-hole)
        "risk_index": 6.0,
        "risk_class": "NP_like_critico",

        # Meta label (famiglia NP_like_critico)
        "meta_label": "NP_like_critico",

        # Compactness / horizon: near-horizon ma horizon_flag ancora falso
        "chi_compactness": 0.70,
        "horizon_flag": False,

        # Global decision (Coq-level view, borderline/amber)
        "loventre_global_decision": "GD_borderline",
        "loventre_global_color": "GC_amber",
        "loventre_global_score": 0.269,
    }


def main() -> None:
    out_path = Path("lmetrics_TSP_crit12_borderline_example.json")
    lmetrics = build_lmetrics_TSPcrit12_borderline()
    with out_path.open("w", encoding="utf-8") as f:
        json.dump(lmetrics, f, indent=2, sort_keys=True, ensure_ascii=False)

    print("[OK] File LMetrics borderline di esempio scritto in:")
    print(f"     {out_path}")
    print("     Chiavi principali:")
    for k in sorted(lmetrics.keys()):
        print(f"       - {k}")


if __name__ == "__main__":
    main()

