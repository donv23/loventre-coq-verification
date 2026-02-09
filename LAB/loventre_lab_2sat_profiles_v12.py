#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
loventre_lab_2sat_profiles_v12.py
---------------------------------------
Generatore profili 2-SAT per LAB V12.

Tre universi minimi:
• EASY (P_ACC-ish)
• CRIT (SAFE-ish)
• HARD (BLACKHOLE-ish)

Questa è solo una palestra: nessun impatto sul core.
"""

from loventre_lab_bridge_v12 import decide_lab_bridge_v12


def run_lab_2sat_easy_profile_v12():
    """
    EASY = P_ACC-ish
    """
    return decide_lab_bridge_v12(kappa_eff=3.0, entropy_eff=1.0)


def run_lab_2sat_crit_profile_v12():
    """
    CRIT = SAFE-only (nessun access boost)
    """
    return decide_lab_bridge_v12(kappa_eff=0.6, entropy_eff=2.0)


def run_lab_2sat_hard_profile_v12():
    """
    HARD = BLACKHOLE-ish
    """
    return decide_lab_bridge_v12(kappa_eff=-1.5, entropy_eff=1.0)


def demo():
    print("=== DEMO LAB V12 2-SAT PROFILES ===")
    print("EASY (P_ACC-ish):      ", run_lab_2sat_easy_profile_v12())
    print("CRIT (SAFE-only):      ", run_lab_2sat_crit_profile_v12())
    print("HARD (BLACKHOLE-ish):  ", run_lab_2sat_hard_profile_v12())


if __name__ == "__main__":
    demo()

