#!/usr/bin/env python3
"""
Loventre Normalize Witness Batch (V60c)
Converte JSON grezzi (ACCESS / SAFE / BH) in LMetrics v3 Coq-ready.
Nessuna sovrascrittura. Nessuna cancellazione.
Produce uno JSON LMetrics per file.
"""

import os
import json
from pathlib import Path
from datetime import datetime
from loventre_policy_bridge import classify_point

ROOT = Path(__file__).parent
WITNESS_DIR = ROOT / "JSON_IO" / "WITNESS"
EXPORT_DIR = Path(
    "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/JSON_IO/LMetrics_v3_for_Coq"
)

EXPORT_DIR.mkdir(parents=True, exist_ok=True)

def load_witness(fp: Path):
    try:
        with open(fp, "r") as f:
            return json.load(f)
    except Exception:
        return None

def record_to_lmetrics(rec):
    """Restituisce dict compatibile LMetrics v3."""
    return {
        "timestamp": rec.get("timestamp"),
        "param": rec.get("param"),
        "factor": rec.get("factor"),
        "kappa_eff": rec.get("kappa_eff"),
        "entropy_eff": rec.get("entropy_eff"),
        "V0": rec.get("V0"),
        "p_tunnel": rec.get("p_tunnel"),
        # campi minimi di policy bridge
        "class": classify_point(rec),
    }

def export_lmetrics(rec, rec_type):
    """Scrive singolo file LMetrics convertito."""
    ts = rec["timestamp"].replace(":", "-").replace(".", "-")
    fname = f"lmetrics_for_coq_{rec_type}_{ts}.json"
    out = EXPORT_DIR / fname
    with open(out, "w") as f:
        json.dump(rec, f, indent=2)
    return out

def main():
    files = sorted(WITNESS_DIR.glob("*.json"))
    if not files:
        print("⚠ Nessun witness da esportare.")
        return

    written = 0
    for fp in files:
        data = load_witness(fp)
        if not data:
            print(f"⚠ Errore lettura: {fp.name}")
            continue

        cls = classify_point(data)
        rec = record_to_lmetrics(data)
        out = export_lmetrics(rec, cls)
        written += 1
        print(f"📤 {fp.name} → {out.name}")

    print(f"\n✨ EXPORT COMPLETE — Written {written} LMetrics files.")

if __name__ == "__main__":
    main()

