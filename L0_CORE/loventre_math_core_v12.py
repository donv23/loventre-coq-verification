#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
loventre_math_core_v12.py
---------------------------------------
Funzioni matematiche *di base* e *neutrali*.

⚠️ Nessuna soglia, nessuna policy, nessun colore.
✔ Operazioni atomiche sicure e riutilizzabili.
✔ Appartiene al CORE e non al LAB.
"""

def safe_div(num, den, default=None):
    """
    Divisione sicura.
    - Se den==0 restituisce default (None di default)
    - Non lancia eccezioni
    """
    try:
        if den == 0:
            return default
        return num / den
    except Exception:
        return default


def clamp01(x):
    """
    Clamping generico in [0,1].
    - None → None
    - numeri >1 → 1
    - numeri <0 → 0
    """
    if x is None:
        return None
    try:
        if x < 0:
            return 0.0
        if x > 1:
            return 1.0
        return float(x)
    except Exception:
        return None


def weighted_sum(values, weights=None):
    """
    Somma pesata generica.
    - values: lista di numeri (o None)
    - weights: lista di pesi (o None → tutti 1)
    - None viene ignorato
    - risultato None se non ci sono valori validi
    """
    if not values:
        return None

    if weights is None:
        weights = [1] * len(values)

    acc = 0.0
    tot = 0.0
    for val, w in zip(values, weights):
        if val is None:
            continue
        acc += val * w
        tot += w

    if tot == 0:
        return None

    return acc / tot

