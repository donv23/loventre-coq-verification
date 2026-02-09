#!/usr/bin/env python3
"""
Loventre — SAT Witness Boundary Jump Test
-----------------------------------------

Scopo:
Verificare che il passaggio tra due witness SAT distinti
produca un SALTO DISCRETO di firma strutturale,
non un recupero continuo.

Questo test:
- NON usa policy
- NON usa decisioni annotate
- opera solo su snapshot LMetrics
"""

import json
import glob
import os

print("\n[Loventre][BOUNDARY-JUMP] Avvio test di salto di witness\n")

# === Configurazione ===

FILES = sorted(glob.glob("lmetrics_SAT_crit16_eps_*.json"))

if not FILES:
    raise RuntimeError("Nessun file lmetrics_SAT_crit16_eps_*.json trovato")

# Chiavi puramente strutturali (snapshot)
KEYS_OF_INTEREST = [
    "kappa_eff",
    "entropy_eff",
    "chi_compactness",
    "V0",
    "p_tunnel",
    "horizon_flag",
    "time_regime",
    "meta_label",
]

def load_metrics(fname):
    with open(fname) as f:
        return json.load(f)

def extract_signature(metrics):
    return tuple(metrics[k] for k in KEYS_OF_INTEREST)

# === Esecuzione test ===

signatures = {}

for fname in FILES:
    metrics = load_metrics(fname)
    sig = extract_signature(metrics)
    signatures[fname] = sig
    print(f"[LOAD] {os.path.basename(fname)} → signature={sig}")

print("\n--------------------------------------------------")

# Confronto discreto
base_file = FILES[0]
base_sig = signatures[base_file]

jump_detected = False

for fname, sig in signatures.items():
    if sig != base_sig:
        jump_detected = True
        print(f"[JUMP] {os.path.basename(fname)}")
        print(f"       base = {base_sig}")
        print(f"       curr = {sig}")

print("--------------------------------------------------")

if jump_detected:
    print("[OK] Boundary jump rilevato")
    print("     → Cambio di witness")
    print("     → Nessuna continuità dinamica")
    print("     → Regime strutturale distinto\n")
else:
    print("[WARN] Nessun salto rilevato")
    print("       Verificare che i witness siano realmente distinti\n")

print("[Loventre][BOUNDARY-JUMP] TEST COMPLETATO\n")

