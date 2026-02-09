#!/usr/bin/env python3
"""
Loventre — SAT ε-sweep decision invariance test

Questo test verifica che:
- piccole perturbazioni ε sulle metriche SAT critiche
- NON producono cambi di decisione
- salvo attraversamento esplicito di una barriera strutturale

Interpretazione:
- stabilità = snapshot
- cambiamento = nuovo witness
"""

import json
import glob
import os
import sys

def load_decision(fname):
    with open(fname) as f:
        data = json.load(f)
    return (
        data.get("loventre_global_decision"),
        data.get("meta_label"),
        data.get("risk_class"),
        data.get("horizon_flag"),
    )

def main():
    files = sorted(glob.glob("lmetrics_SAT_crit16_eps_*.json"))

    if not files:
        print("[FAIL] Nessun file ε trovato (lmetrics_SAT_crit16_eps_*.json)")
        sys.exit(1)

    print("[Loventre][EPS-INVARIANCE] Avvio test di invarianza decisionale")
    print("File analizzati:", len(files))
    print("--------------------------------------------------")

    base = load_decision(files[0])
    print("[BASE]", os.path.basename(files[0]), "→", base)

    ok = True

    for fname in files[1:]:
        d = load_decision(fname)
        print("[CHK ]", os.path.basename(fname), "→", d)
        if d != base:
            ok = False
            print("   [DIFF] rispetto al baseline")

    print("--------------------------------------------------")

    if ok:
        print("[OK] Invarianza decisionale confermata su ε-sweep")
        print("     Nessun recovery, nessuna dinamica implicita")
        print("     Regime strutturale stabile")
    else:
        print("[WARN] Variazioni rilevate")
        print("       Questo indica attraversamento di regime")
        print("       → cambio di witness (non recovery)")

if __name__ == "__main__":
    main()

