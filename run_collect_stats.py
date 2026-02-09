"""
LOVENTRE ENGINE — COLLECT + POLICY + STATS (Random Mode)
Versione 2026-01-12 — Vincenzo Loventre + ChatGPT
- Chiama il meta engine random
- Classifica ogni punto con Policy Bridge
- Aggiorna STATS cumulativi + TREND timeline
"""

import json
import os
from datetime import datetime

from loventre_meta_engine_random import compute_random_metrics
from loventre_policy_bridge import classify_point

STATS_DIR = "STATS"
TREND_DIR = os.path.join(STATS_DIR, "TREND")

CUMULATIVE_PATH = os.path.join(STATS_DIR, "stats_cumulative.json")
TIMELINE_PATH = os.path.join(TREND_DIR, "timeline.csv")

os.makedirs(STATS_DIR, exist_ok=True)
os.makedirs(TREND_DIR, exist_ok=True)

def load_stats():
    if not os.path.exists(CUMULATIVE_PATH):
        return {
            "cycles": 0,
            "SAFE": 0,
            "ACCESS": 0,
            "BH": 0,
            "last_event": None,
            "started": datetime.utcnow().isoformat()
        }
    with open(CUMULATIVE_PATH, "r") as f:
        return json.load(f)

def save_stats(stats):
    with open(CUMULATIVE_PATH, "w") as f:
        json.dump(stats, f, indent=2)

def append_timeline(cycle, label_counts):
    ts = datetime.utcnow().isoformat()
    row = f"{ts},{cycle},{label_counts['SAFE']},{label_counts['ACCESS']},{label_counts['BH']}\n"
    new_file = not os.path.exists(TIMELINE_PATH)
    with open(TIMELINE_PATH, "a") as f:
        if new_file:
            f.write("timestamp,cycle,SAFE,ACCESS,BH\n")
        f.write(row)

if __name__ == "__main__":
    stats = load_stats()

    # 1) compute new random point
    point = compute_random_metrics()

    # 2) classify via policy bridge
    label = classify_point(point)

    if label == "SAFE":
        stats["SAFE"] += 1
    elif label == "ACCESS":
        stats["ACCESS"] += 1
    elif label == "BH":
        stats["BH"] += 1

    stats["cycles"] += 1
    stats["last_event"] = label

    save_stats(stats)

    append_timeline(stats["cycles"], stats)

    print(f"📊 LOVENTRE ENGINE — STATS + EXEC")
    print(f"[Cycle {stats['cycles']}]  SAFE={stats['SAFE']}  ACCESS={stats['ACCESS']}  BH={stats['BH']}")
    print(f"🔥 Last point classified as: {label}")

