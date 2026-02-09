#!/usr/bin/env python3
"""
LOVENTRE ENGINE LIVE COUNTER (v1)
Gira per sempre come run_forever.py
ma conta e stampa le classi osservate:
SAFE, ACCESSIBLE, BLACKHOLE
e salva un report periodico.
"""

import json
import time
from datetime import datetime
from loventre_meta_engine import run_loventre_meta_engine

SAFE = 0
ACCESS = 0
BH = 0

report_file = "loventre_live_counter_report.jsonl"

print("🔥 LOVENTRE ENGINE — LIVE COUNTER MODE")

cycle = 0
while True:
    cycle += 1
    metrics = run_loventre_meta_engine()

    label = metrics.get("meta_label", "unknown").lower()

    if "black" in label:
        BH += 1
    elif "access" in label:
        ACCESS += 1
    else:
        SAFE += 1

    print(f"[Cycle {cycle}]  SAFE={SAFE}  ACCESS={ACCESS}  BH={BH}")

    snapshot = {
        "cycle": cycle,
        "timestamp": datetime.utcnow().isoformat(),
        "safe": SAFE,
        "accessible": ACCESS,
        "blackhole": BH,
        "last_label": label
    }

    with open(report_file, "a") as f:
        f.write(json.dumps(snapshot) + "\n")

    time.sleep(1)

