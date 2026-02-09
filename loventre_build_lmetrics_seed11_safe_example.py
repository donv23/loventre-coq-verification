#!/usr/bin/env python3
"""
LOVENTRE ENGINE – LMetrics example for seed (param=1, factor=1) SAFE / P_like
=============================================================================

Questo script costruisce un esempio concreto di bus LMetrics per il seed
(param=1, factor=1) della seed_grid, che è:

  - region regular, P_like = True, NP_like = False
  - kappa_eff = 0.0
  - entropy_eff ≈ 0.060
  - V0 ≈ 0.0602
  - p_tunnel ≈ 1.0
  - P_success ≈ 1.0
  - time_regime = time_euclidean
  - risk_class = LOW
  - meta_label = P_like_like
  - curvatura quasi-euclidea, compattezza bassa

A livello globale Loventre lo consideriamo un caso SAFE:

  - loventre_global_decision = GD_safe
  - loventre_global_color = GC_green
  - loventre_global_score = 1.0
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Dict, Any


def build_lmetrics_seed11_safe() -> Dict[str, Any]:
    """Costruisce il dict che rappresenta m_seed11_safe a livello LMetrics."""
    return {
        # Core geometric / energetic metrics (seed regular, P_like)
        "kappa_eff": 0.0,
        "entropy_eff": 0.060,
        "V0": 0.0602,
        "a_min": 1.0,

        # Tunneling and success probability (quasi-euclideo, altamente accessibile)
        "p_tunnel": 1.0,
        "P_success": 1.0,

        # Relativistic / mass-like indices (dinamica leggera, euclidea)
        "gamma_dilation": 1.015,
        "time_regime": "time_euclidean",
        "mass_eff": 1.0,
        "inertial_idx": 1.0,

        # Risk metrics (LOW risk)
        "risk_index": 2.0,
        "risk_class": "LOW",

        # Meta label: famiglia P_like_like
        "meta_label": "P_like_like",

        # Compactness / horizon: decisamente subcritico
        "chi_compactness": 0.20,
        "horizon_flag": False,

        # Global decision (Coq-level view, safe/green)
        "loventre_global_decision": "GD_safe",
        "loventre_global_color": "GC_green",
        "loventre_global_score": 1.0,
    }


def main() -> None:
    out_path = Path("lmetrics_seed11_safe_example.json")
    lmetrics = build_lmetrics_seed11_safe()
    with out_path.open("w", encoding="utf-8") as f:
        json.dump(lmetrics, f, indent=2, sort_keys=True, ensure_ascii=False)

    print("[OK] File LMetrics SAFE di esempio scritto in:")
    print(f"     {out_path}")
    print("     Chiavi principali:")
    for k in sorted(lmetrics.keys()):
        print(f"       - {k}")


if __name__ == "__main__":
    main()

