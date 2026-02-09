#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
loventre_lab_metrics_v12.py
------------------------------------
Calcolo delle metriche grezze V12.
Sandbox: non interagisce con bus, policy o JSON.

• Bucato minimo: solo kappa_eff, entropy_eff
• Derivati semplici
• Nessun side effect
"""

def compute_lab_metrics_v12(kappa_eff=None, entropy_eff=None):
    """
    Restituisce un dizionario minimo di metriche LAB V12.
    È sandbox: se i valori non ci sono restano None o safe default.
    """

    # curvatura locale molto semplice
    curvature_grad = None
    if kappa_eff is not None:
        curvature_grad = kappa_eff * 0.1

    # entropia localizzata grezza
    entropy_local = None
    if entropy_eff is not None:
        entropy_local = entropy_eff * 0.05

    # black hole “escape score” minimale
    bh_escape_score = None
    if kappa_eff is not None and kappa_eff < 0:
        bh_escape_score = 0.0  # nessuna fuga nel LAB

    return {
        "kappa_eff": kappa_eff,
        "entropy_eff": entropy_eff,
        "curvature_grad": curvature_grad,
        "entropy_local": entropy_local,
        "bh_escape_score": bh_escape_score,
        "meta_label_v12": "LAB_v12_metric",
    }


def demo():
    print("=== DEMO V12 LAB METRICS ===")

    safe_case = compute_lab_metrics_v12(2.0, 4.0)
    print("SAFE-ish:", safe_case)

    bh_case = compute_lab_metrics_v12(-1.2, None)
    print("BH-ish:", bh_case)

    none_case = compute_lab_metrics_v12()
    print("None-case:", none_case)


if __name__ == "__main__":
    demo()

