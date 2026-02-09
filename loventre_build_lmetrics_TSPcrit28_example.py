#!/usr/bin/env python3
"""
LOVENTRE ENGINE – LMetrics example for TSP_crit_28
==================================================

Questo script costruisce un esempio concreto di bus LMetrics
per una istanza NP_like_black_hole tipo TSP_crit_28, usando
i valori numerici visti nelle tabelle del motore:

  n_cities  kappa_eff  entropy_eff   V0       a_min   p_tunnel(E)   E[N]
        28     0.950     0.930  3.5495    4.50    1.494e-07    6.692e+06
         P_success   gamma_dil  mass_eff  inert_idx   time_regime  decision
         1.494e-04     16.72     2.415     40.370   time_hyperbolic RITIRA RED

Più il blocco globale:

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


def build_lmetrics_TSPcrit28() -> Dict[str, Any]:
    """Costruisce il dict che rappresenta m_TSPcrit28 a livello LMetrics."""
    return {
        # Core geometric / energetic metrics
        "kappa_eff": 0.950,
        "entropy_eff": 0.930,
        "V0": 3.5495,
        "a_min": 4.50,

        # Tunneling and success probability
        "p_tunnel": 1.494e-07,
        "P_success": 1.494e-04,

        # Relativistic / mass-like indices
        "gamma_dilation": 16.72,
        "time_regime": "time_hyperbolic",
        "mass_eff": 2.415,
        "inertial_idx": 40.370,

        # Risk metrics
        "risk_index": 9.5,
        "risk_class": "NP_like_black_hole",

        # Meta label (famiglia NP_like-critica / black-hole)
        "meta_label": "NP_like_black_hole",

        # Compactness / horizon
        "chi_compactness": 0.95,
        "horizon_flag": True,

        # Global decision (Coq-level view)
        # Qui usiamo i nomi dei costruttori Coq come stringhe:
        #   GD_critical  ~ "critical" lato Policy Bridge
        #   GC_red       ~ "RED" lato motore operativo
        "loventre_global_decision": "GD_critical",
        "loventre_global_color": "GC_red",
        "loventre_global_score": 0.001,
    }


def main() -> None:
    out_path = Path("lmetrics_TSP_crit28_example.json")
    lmetrics = build_lmetrics_TSPcrit28()
    with out_path.open("w", encoding="utf-8") as f:
        json.dump(lmetrics, f, indent=2, sort_keys=True, ensure_ascii=False)

    print("[OK] File LMetrics di esempio scritto in:")
    print(f"     {out_path}")
    print("     Chiavi principali:")
    for k in sorted(lmetrics.keys()):
        print(f"       - {k}")


if __name__ == "__main__":
    main()

