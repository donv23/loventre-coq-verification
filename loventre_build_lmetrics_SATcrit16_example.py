#!/usr/bin/env python3
"""
LOVENTRE ENGINE – LMetrics example for SAT_crit_16
==================================================

Questo script costruisce un esempio concreto di bus LMetrics
per una istanza NP_like_black_hole tipo SAT_crit16, usando
i valori numerici visti nelle tabelle del motore:

  name        n_vars  clauses  kappa_eff  entropy_eff   V0       a_min
  sat_crit16      16       29     0.930     0.930  3.4596    4.30

      p_tunnel(E)   E[N]          P_success   gamma_dil  mass_eff  inert_idx
      3.755e-07    2.663e+06  3.754e-04       15.79     2.395       37.829

      time_regime        decision
      time_hyperbolic    Quasi impossibile (NP_like_black_hole)

Più il blocco globale concettuale:

  risk_class                 = NP_like_black_hole
  meta_label                 = NP_like_black_hole
  horizon_flag               = True
  loventre_global_decision   = GD_critical
  loventre_global_color      = GC_red
  loventre_global_score      = 0.001

Il JSON prodotto ha le stesse chiavi del record Coq LMetrics:

  kappa_eff, entropy_eff, V0, a_min,
  p_tunnel, P_success,
  gamma_dilation, time_regime,
  mass_eff, inertial_idx,
  risk_index, risk_class,
  meta_label,
  chi_compactness, horizon_flag,
  loventre_global_decision, loventre_global_color, loventre_global_score
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Dict, Any


def build_lmetrics_SATcrit16() -> Dict[str, Any]:
    """Costruisce il dict che rappresenta m_SATcrit16 a livello LMetrics."""
    return {
        # Core geometric / energetic metrics
        "kappa_eff": 0.930,
        "entropy_eff": 0.930,
        "V0": 3.4596,
        "a_min": 4.30,

        # Tunneling and success probability
        "p_tunnel": 3.755e-07,
        "P_success": 3.754e-04,

        # Relativistic / mass-like indices
        "gamma_dilation": 15.79,
        "time_regime": "time_hyperbolic",
        "mass_eff": 2.395,
        "inertial_idx": 37.829,

        # Risk metrics (NP_like black-hole regime)
        "risk_index": 9.3,
        "risk_class": "NP_like_black_hole",

        # Meta label (famiglia NP_like-critica / black-hole)
        "meta_label": "NP_like_black_hole",

        # Compactness / horizon
        "chi_compactness": 0.93,
        "horizon_flag": True,

        # Global decision (Coq-level view)
        #   GD_critical  ~ "critical" lato Policy Bridge
        #   GC_red       ~ "RED" lato motore operativo
        "loventre_global_decision": "GD_critical",
        "loventre_global_color": "GC_red",
        "loventre_global_score": 0.001,
    }


def main() -> None:
    out_path = Path("lmetrics_SAT_crit16_example.json")
    lmetrics = build_lmetrics_SATcrit16()
    with out_path.open("w", encoding="utf-8") as f:
        json.dump(lmetrics, f, indent=2, sort_keys=True, ensure_ascii=False)

    print("[OK] File LMetrics di esempio scritto in:")
    print(f"     {out_path}")
    print("     Chiavi principali:")
    for k in sorted(lmetrics.keys()):
        print(f"       - {k}")


if __name__ == "__main__":
    main()

