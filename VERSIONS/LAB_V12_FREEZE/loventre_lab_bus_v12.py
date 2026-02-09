#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
loventre_lab_bus_v12.py
---------------------------------------------------
LAB BUS sandbox V12

• Riceve metriche + potenziale dal pipeline
• Aggiunge una classificazione ultra semplice
• Fornisce la API pubblica run_lab_bus_v12()
"""

from loventre_lab_pipeline_v12 import run_lab_pipeline_v12


def classify_bus_state_v12(snapshot: dict) -> str:
    """
    Classifica minima sulla base di kappa_eff
    """
    k = snapshot.get("kappa_eff")

    if k is None:
        return "UNDEFINED-ish"
    if k < 0:
        return "BLACKHOLE-ish"
    if k > 1.5:
        return "P_ACC-ish"
    return "SAFE-ish"


def run_lab_bus_v12(kappa_eff=None, entropy_eff=None) -> dict:
    """
    API di bus V12: pipeline minima + classificazione sandbox
    """
    snap = run_lab_pipeline_v12(kappa_eff=kappa_eff,
                                entropy_eff=entropy_eff)

    bus_state = classify_bus_state_v12(snap)

    enriched = {
        **snap,
        "bus_state": bus_state,
        "meta_label_v12": "LAB_v12_bus"
    }

    return enriched


def demo():
    print("=== DEMO V12 LAB BUS ===")

    safe_case = run_lab_bus_v12(2.0, 4.0)
    print("SAFE-ish:", safe_case)

    bh_case = run_lab_bus_v12(-1.2, None)
    print("BH-ish:", bh_case)

    none_case = run_lab_bus_v12()
    print("None-case:", none_case)


if __name__ == "__main__":
    demo()

