#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
loventre_lab_potential_v12.py
------------------------------------
Modulo LAB isolato (V12).
Calcola un potenziale U grezzo usando solo kappa e entropia.

⚠️ Non tocca il core
⚠️ Non scrive JSON
⚠️ Nessuna dipendenza da altri layer
⚠️ Nessuna policy
⚠️ 100% sandbox
"""

def compute_lab_potential_v12(kappa_eff=None, entropy_eff=None,
                              alpha=0.5, beta=0.5):
    """
    Calcola un potenziale semplice: U = alpha*kappa + beta*entropy.

    Restituisce sempre un dict autosufficiente e annotato V12.
    """
    # normalizza None
    k = kappa_eff if kappa_eff is not None else 0.0
    e = entropy_eff if entropy_eff is not None else 0.0

    U = alpha * k + beta * e

    return {
        "kappa_eff": kappa_eff,
        "entropy_eff": entropy_eff,
        "alpha": alpha,
        "beta": beta,
        "U": U,
        "meta_label_v12": "LAB_v12_potential"
    }


def demo():
    """
    Piccolo test locale per V12.
    Non dipende da regressione o bus del motore.
    """
    print("=== DEMO V12 LAB POTENTIAL ===")

    safe_case = compute_lab_potential_v12(kappa_eff=2.0, entropy_eff=4.0)
    print("SAFE-ish case:", safe_case)

    bh_case = compute_lab_potential_v12(kappa_eff=-1.2, entropy_eff=None)
    print("BH-ish case:", bh_case)

    none_case = compute_lab_potential_v12()
    print("None case:", none_case)


if __name__ == "__main__":
    demo()

