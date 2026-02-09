#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
loventre_labels_core_v12.py
---------------------------
Label e colori canonici V12.

L0_CORE → verità fondamentale
Nessuna logica, solo costanti simboliche.
"""

# Strato decisione base
SAFE = "SAFE"
SAFE_ACCESSIBLE = "SAFE_ACCESSIBLE"
BLACKHOLE = "BLACKHOLE"
WAIT = "WAIT"

# Strato colori (visuale, opzionale)
COLOR_GREEN = "GREEN"
COLOR_BLUE = "BLUE"
COLOR_RED = "RED"
COLOR_YELLOW = "YELLOW"

# Strato “ish” per i layer superiori (nuovo per L1/L2/L3)
SAFE_ISH = "SAFE-ish"
P_ACC_ISH = "P_ACC-ish"
BLACKHOLE_ISH = "BLACKHOLE-ish"
UNDEFINED_ISH = "UNDEFINED-ish"

def demo():
    print("=== DEMO LABELS CORE V12 ===")
    base = [SAFE, SAFE_ACCESSIBLE, BLACKHOLE, WAIT]
    colors = [COLOR_GREEN, COLOR_BLUE, COLOR_RED, COLOR_YELLOW]
    ish = [SAFE_ISH, P_ACC_ISH, BLACKHOLE_ISH, UNDEFINED_ISH]
    print(base)
    print(colors)
    print(ish)

if __name__ == "__main__":
    demo()

