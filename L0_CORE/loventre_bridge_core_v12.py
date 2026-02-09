#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
loventre_bridge_core_v12.py
------------------------------------------------
Core bridge V12: decision → color → score.

Questo modulo NON dipende dal LAB.
Tutti gli import sono assoluti nel namespace L0_CORE.
"""

from L0_CORE.loventre_labels_core_v12 import (
    COLOR_GREEN,
    COLOR_YELLOW,
    COLOR_RED,
    COLOR_BLUE,
)
from L0_CORE.loventre_utils_core_v12 import clamp01


def pack_bridge_v12(bridge_decision_v12, bus_state=None):
    """
    Trasforma una decisione V12 in una tripla:
      (colore, score, decisione)
    Restituisce un dict coerente.
    """

    if bridge_decision_v12 == "SAFE_ACCESSIBLE":
        color = COLOR_BLUE
        score = 1.0
    elif bridge_decision_v12 == "SAFE":
        color = COLOR_GREEN
        score = 0.8
    elif bridge_decision_v12 == "BLACKHOLE":
        color = COLOR_RED
        score = 0.0
    else:
        color = COLOR_YELLOW
        score = 0.5

    return {
        "bridge_decision_v12": bridge_decision_v12,
        "bridge_color_v12": color,
        "bridge_score_v12": clamp01(score),
        "meta_label_v12": "CORE_bridge_v12",
    }


def demo():
    print("=== DEMO CORE BRIDGE V12 ===")
    for dec in ["SAFE", "SAFE_ACCESSIBLE", "BLACKHOLE", "WAIT"]:
        out = pack_bridge_v12(dec)
        print(out)


if __name__ == "__main__":
    demo()

