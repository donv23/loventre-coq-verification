#!/usr/bin/env python3
"""
LOVENTRE ENGINE — TREND ANALYSIS LOOP (v1)
Conta le classi come run_live_counter
MA ogni 50 cicli stampa un TREND:
- %SAFE
- %ACCESSIBLE
- %BLACKHOLE
E salva una serie temporale nel file .jsonl
"""

import json
import time
from datetime import datetime
from loventre_meta_engine import run_loventre_meta_engine

SAFE = 0
ACCESS = 0
BH = 0

cycle = 0

report_file = "loventre_live_trend_report.jsonl"

print("🌿 LOVENTRE ENGINE — LIVE TREND MODE")

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

    # Stampiamo ogni ciclo come prima
    print(f"[Cycle {cycle}] SAFE={SAFE} ACCESS={ACCESS} BH={BH}")

    # Ogni 50 cicli calcoliamo il trend
    if cycle % 50 == 0:
        total = SAFE + ACCESS + BH
        trend = {
            "cycle": cycle,
            "timestamp": datetime.utcnow().isoformat(),
            "safe_pct": SAFE / total,
            "access_pct": ACCESS / total,
            "bh_pct": BH / total,
            "safe_raw": SAFE,
            "access_raw": ACCESS,
            "bh_raw": BH,
        }

        print(f"📊 TREND @ {cycle}: SAFE={trend['safe_pct']:.2f} ACC={trend['access_pct']:.2f} BH={trend['bh_pct']:.2f}")

        with open(report_file, "a") as f:
            f.write(json.dumps(trend) + "\n")

    time.sleep(1)

