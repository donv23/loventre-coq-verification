#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
loventre_lab_pipeline_v12.py
------------------------------------
Pipeline LAB V12 completamente sandbox.

• Usa V12 metrics grezze
• Usa V12 potential grezzo
• Fonde i risultati in un unico dict
• Non modifica il core
• Nessun JSON, nessuna policy, nessun bus

È una palestra controllata per V12.
"""

from loventre_lab_metrics_v12 import compute_lab_metrics_v12
from loventre_lab_potential_v12 import compute_lab_potential_v12

def run_lab_pipeline_v12(kappa_eff=None, entropy_eff=None):
    """
    Esegue un ciclo minimo LAB:
    - metriche grezze
    - potenziale grezzo
    - fusione in un unico snapshot
    """
    metrics = compute_lab_metrics_v12(kappa_eff=kappa_eff,
                                      entropy_eff=entropy_eff)

    potential = compute_lab_potential_v12(kappa_eff=kappa_eff,
                                          entropy_eff=entropy_eff)

    merged = {
        **metrics,
        **potential,
        "meta_label_v12": "LAB_v12_pipeline",
    }

    return merged


def demo():
    print("=== DEMO V12 LAB PIPELINE ===")

    safe_case = run_lab_pipeline_v12(2.0, 4.0)
    print("SAFE-ish:", safe_case)

    bh_case = run_lab_pipeline_v12(-1.2, None)
    print("BH-ish:", bh_case)

    none_case = run_lab_pipeline_v12()
    print("None-case:", none_case)


if __name__ == "__main__":
    demo()

