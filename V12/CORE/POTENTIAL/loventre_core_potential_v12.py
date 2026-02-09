#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
loventre_core_potential_v12.py
------------------------------------
Modulo CORE V12 — Potential Layer
Versione stabile derivata dal LAB V12.

Regole:
• Nessuna dipendenza da altri moduli LAB
• Nessun print
• Nessun accesso a disco
• Nessun side-effect
• Solo: (kappa, entropy) → potential dict

U = alpha*kappa_eff + beta*entropy_eff

DEFAULT:
  alpha = 0.5
  beta  = 0.5
"""

def compute_core_potential_v12(kappa_eff=None, entropy_eff=None,
                               alpha=0.5, beta=0.5):
    """
    Calcolo del potenziale informazionale.
    Restituisce sempre un dict con tutti i campi richiesti.
    """
    if kappa_eff is None and entropy_eff is None:
        U = 0.0
    else:
        k = kappa_eff if kappa_eff is not None else 0.0
        h = entropy_eff if entropy_eff is not None else 0.0
        U = alpha * k + beta * h

    return {
        "kappa_eff": kappa_eff,
        "entropy_eff": entropy_eff,
        "alpha": alpha,
        "beta": beta,
        "U": U,
        "meta_label_v12": "CORE_v12_potential"
    }


def smoke_test():
    safe = compute_core_potential_v12(2.0, 4.0)
    bh   = compute_core_potential_v12(-1.2, None)
    none = compute_core_potential_v12()

    return [safe, bh, none]


if __name__ == "__main__":
    for case in smoke_test():
        print(case)

