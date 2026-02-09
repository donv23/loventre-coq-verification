"""
loventre_json_crosscheck_coq.py
Crosscheck semplice JSON → LMetrics v6
FASE 1: verifica campi obbligatori
(Non richiede ancora compilazione Coq)
"""

import os
import json
from glob import glob

BASE = os.path.expanduser(
    "~/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/JSON_IO/LMetrics_v6_cli_bridge"
)

REQUIRED_FIELDS = [
    "kappa_eff", "mass_eff", "inertial_idx",
    "risk_index", "risk_class",
    "loventre_global_decision", "loventre_global_color", "loventre_global_score",
    "meta_label"
]

def check_json_file(path):
    try:
        with open(path, "r") as f:
            data = json.load(f)
    except Exception as e:
        return (False, f"ERRORE lettura JSON: {e}")

    missing = [k for k in REQUIRED_FIELDS if k not in data]
    if missing:
        return (False, f"Campi mancanti: {missing}")

    return (True, "OK")

def main():
    print("\n===== LOVENTRE JSON ↔ LMetrics CHECK V6 =====\n")
    files = sorted(glob(os.path.join(BASE, "*.json")))

    if not files:
        print(f"[FAIL] Nessun JSON trovato in: {BASE}")
        return

    fails = 0
    for fp in files:
        ok, msg = check_json_file(fp)
        tag = "[ OK ]" if ok else "[FAIL]"
        print(f"{tag} {os.path.basename(fp)} — {msg}")
        if not ok:
            fails += 1

    print("\n===== RISULTATI =====")
    if fails == 0:
        print("TUTTI COERENTI ✔")
    else:
        print(f"{fails} JSON non conformi ❌")
    print("\n===== END JSON ↔ COQ CHECK V6 =====\n")

if __name__ == "__main__":
    main()

