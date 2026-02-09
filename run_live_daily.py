#!/usr/bin/env python3
"""
LOVENTRE ENGINE — DAILY ARCHIVER MODE (v1)
- Mantiene contatori SAFE / ACCESS / BH
- Salva i campioni raw ogni SAMPLE_EVERY cicli
- Quando cambia giorno, chiude il file e ne apre uno nuovo
Questo inaugura l’archiviazione multi-giorno
"""

import json
import time
from datetime import datetime, date
from loventre_meta_engine import run_loventre_meta_engine

SAFE = 0
ACCESS = 0
BH = 0

cycle = 0
SAMPLE_EVERY = 25

current_day = date.today()
file_name = f"loventre_samples_{current_day.isoformat()}.jsonl"

print("🌍 LOVENTRE ENGINE — DAILY MODE")

while True:
    cycle += 1
    metrics = run_loventre_meta_engine()
    label = metrics.get("meta_label", "").lower()

    if "black" in label:
        BH += 1
    elif "access" in label:
        ACCESS += 1
    else:
        SAFE += 1

    print(f"[{current_day} | Cycle {cycle}] SAFE={SAFE} ACCESS={ACCESS} BH={BH}")

    if cycle % SAMPLE_EVERY == 0:
        record = {
            "timestamp": datetime.utcnow().isoformat(),
            "cycle": cycle,
            "metrics": metrics,
            "SAFE": SAFE,
            "ACCESS": ACCESS,
            "BH": BH,
        }
        with open(file_name, "a") as f:
            f.write(json.dumps(record) + "\n")
        print(f"📦 DAILY SAMPLE SAVED @ cycle {cycle}")

    # 🔄 rollover giornaliero
    new_day = date.today()
    if new_day != current_day:
        print(f"📂 New day detected ({new_day}), starting new archive file...")
        current_day = new_day
        file_name = f"loventre_samples_{current_day.isoformat()}.jsonl"
        SAFE = 0
        ACCESS = 0
        BH = 0
        cycle = 0

    time.sleep(1)

