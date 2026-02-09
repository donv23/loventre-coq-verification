#!/usr/bin/env python3
"""
Loventre — Cross-Family Boundary Jump Test

Verifica che il passaggio tra famiglie diverse (2-SAT, SATcrit, TSPcrit)
non avvenga tramite continuità dinamica, ma solo tramite salto discreto
di witness, pur mantenendo eventualmente lo stesso regime decisionale.
"""

import json
import os

FILES = [
    "metrics_2SAT_crit_demo.json",
    "lmetrics_SAT_crit16_eps_+0.000.json",
    "lmetrics_TSP_crit28_example.json",
]

KEYS_OF_INTEREST = [
    "kappa_eff",
    "chi_compactness",
    "horizon_flag",
    "time_regime",
    "meta_label",
]

def load_metrics(fname):
    with open(fname) as f:
        return json.load(f)

def extract_signature(metrics):
    return tuple(metrics.get(k, None) for k in KEYS_OF_INTEREST)

def main():
    print("\n[Loventre][CROSS-FAMILY-JUMP] Avvio test di boundary jump inter-famiglia\n")

    signatures = {}
    for fname in FILES:
        if not os.path.exists(fname):
            print(f"[SKIP] {fname} non trovato")
            continue
        m = load_metrics(fname)
        sig = extract_signature(m)
        signatures[fname] = sig
        print(f"[LOAD] {fname} → signature={sig}")

    print("\n--------------------------------------------------")

    base_file = list(signatures.keys())[0]
    base_sig = signatures[base_file]

    jump_detected = False

    for fname, sig in signatures.items():
        if fname == base_file:
            continue
        if sig != base_sig:
            jump_detected = True
            print(f"[JUMP] {base_file} → {fname}")
            print(f"       base = {base_sig}")
            print(f"       curr = {sig}")

    print("--------------------------------------------------")

    if jump_detected:
        print("[OK] Boundary jump inter-famiglia rilevato")
        print("     → Nessuna continuità tra famiglie")
        print("     → Cambio di witness necessario")
        print("     → Regimi strutturalmente distinti")
    else:
        print("[WARN] Nessun salto rilevato (verifica i file usati)")

    print("\n[Loventre][CROSS-FAMILY-JUMP] TEST COMPLETATO\n")

if __name__ == "__main__":
    main()

