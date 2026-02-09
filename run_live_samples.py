#!/usr/bin/env python3
"""
LOVENTRE ENGINE — SAMPLE CAPTURE MODE (v1)
Mantiene contatori come run_live_trend
E salva ogni N cicli un campione reale del metrics bus
Questo è un passo critico verso il “teorema empirico iterato”
"""

import json
import time
from datetime import datetime
from loventre_meta_engine import run_loventre_meta_engine

SAFE = 0
ACCESS = 0
BH = 0

cycle = 0

# Dove salvare i campioni
sample_file = "loventre_samples.jsonl"
SAMPLE_EVERY = 25  # ogni 25 cicli salviamo un campione

print("🌱 LOVENTRE ENGINE — LIVE SAMPLE MODE")

while True:
    cycle += 1
    metrics = run_loventre_meta_engine()
    label = metrics.get("meta_label", "").lower()

    # contatori per classi
    if "black" in label:
        BH += 1
    elif "access" in label:
        ACCESS += 1
    else:
        SAFE += 1

    print(f"[Cycle {cycle}] SAFE={SAFE} ACCESS={ACCESS} BH={BH}")

    # ogni SAMPLE_EVERY cicli salviamo snapshot
    if cycle % SAMPLE_EVERY == 0:
        record = {
            "cycle": cycle,
            "timestamp": datetime.utcnow().isoformat(),
            "metrics": metrics
        }
        with open(sample_file, "a") as f:
            f.write(json.dumps(record) + "\n")
        print(f"📦 SAMPLE SAVED @ cycle {cycle}")

    time.sleep(1)

