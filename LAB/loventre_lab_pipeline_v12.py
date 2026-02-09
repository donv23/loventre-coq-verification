#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
loventre_lab_pipeline_v12.py  (L1 aligned FINAL)
--------------------------------------------------
Usa:
  • compute_l1_metrics_v12 (L1)
  • compute_lab_potential_v12
Fonde i risultati in un unico dict.
"""

from L1_METRICS.loventre_metrics_l1_v12 import compute_l1_metrics_v12
from LAB.loventre_lab_potential_v12 import compute_lab_potential_v12


def run_lab_pipeline_v12(kappa=None, entropy=None):
    """
    Pipeline minima V12:
    1) L1 metriche
    2) potenziale su kappa L1
    3) fusione in uno snapshot
    """
    # 1) calcolo L1
    l1 = compute_l1_metrics_v12(raw_value=kappa)

    # 2) potenziale basato su kappa_l1
    potential = compute_lab_potential_v12(
        kappa_eff=l1["kappa_l1"],
        entropy_eff=entropy
    )

    merged = {
        **l1,
        **potential,
        "meta_label_v12": "LAB_v12_pipeline",
    }
    return merged


def demo():
    print("=== DEMO V12 LAB PIPELINE (L1-aligned, FINAL) ===")
    for k in [2.0, 0.3, -1.0, None]:
        out = run_lab_pipeline_v12(kappa=k, entropy=None)
        print(f"kappa={str(k):>4} → {out}")


if __name__ == "__main__":
    demo()

