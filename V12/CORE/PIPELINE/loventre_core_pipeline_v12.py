#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
loventre_core_pipeline_v12.py
--------------------------------------
CORE V12 — Pipeline
Promosso dal LAB.

Combina:
 • Metrics CORE V12
 • Potential CORE V12

Regole:
 • Zero dipendenze dal LAB
 • Nessun print (salvo smoke test)
 • Nessuna scrittura su disco
 • Restituisce un unico dict
"""

import os
import sys

# ===== hack definitivo V12: aggiungi root repo reale al PYTHONPATH =====
HERE = os.path.abspath(os.path.dirname(__file__))                  # .../V12/CORE/PIPELINE
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))            # .../V12
REPO = os.path.abspath(os.path.join(HERE, "..", "..", ".."))      # .../loventre_engine_clean_seed

for p in (ROOT, REPO):
    if p not in sys.path:
        sys.path.append(p)

# ===== import assoluto ora funziona =====
from V12.CORE.POTENTIAL.loventre_core_potential_v12 import compute_core_potential_v12


def compute_core_metrics_v12(kappa_eff=None, entropy_eff=None):
    """
    Placeholder del CORE V12 metric layer.
    Sganciato dal LAB ma matematica coerente.
    """
    if kappa_eff is None:
        curvature_grad = None
    else:
        curvature_grad = 0.1 * kappa_eff

    if entropy_eff is None:
        entropy_local = None
    else:
        entropy_local = 0.05 * entropy_eff

    bh_escape_score = None if (kappa_eff is not None and kappa_eff > 0) else 0.0

    return {
        "kappa_eff": kappa_eff,
        "entropy_eff": entropy_eff,
        "curvature_grad": curvature_grad,
        "entropy_local": entropy_local,
        "bh_escape_score": bh_escape_score,
        "meta_label_v12": "CORE_v12_metrics",
    }


def compute_core_pipeline_v12(kappa_eff=None, entropy_eff=None):
    """
    Combina metriche CORE + potenziale CORE in un unico pacchetto.
    """
    metrics = compute_core_metrics_v12(
        kappa_eff=kappa_eff,
        entropy_eff=entropy_eff,
    )

    potential = compute_core_potential_v12(
        kappa_eff=kappa_eff,
        entropy_eff=entropy_eff,
    )

    merged = {
        **metrics,
        **potential,
        "meta_label_v12": "CORE_v12_pipeline",
    }
    return merged


def smoke_test():
    safe = compute_core_pipeline_v12(2.0, 4.0)
    bh   = compute_core_pipeline_v12(-1.2, None)
    none = compute_core_pipeline_v12()
    return [safe, bh, none]


if __name__ == "__main__":
    for item in smoke_test():
        print(item)

