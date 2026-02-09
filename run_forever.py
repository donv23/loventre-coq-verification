import json
import time
from datetime import datetime

from loventre_meta_engine import run_loventre_meta_engine

OUTPUT_FILE = "loventre_live_history.jsonl"

def append_log(entry: dict):
    entry_with_time = {
        "timestamp": datetime.utcnow().isoformat() + "Z",
        "data": entry
    }
    with open(OUTPUT_FILE, "a") as f:
        f.write(json.dumps(entry_with_time) + "\n")

if __name__ == "__main__":
    print("🔥 LOVENTRE ENGINE — LIVE MODE (logging enabled)")
    cycle = 0
    while True:
        cycle += 1
        print(f"[Cycle {cycle}] executing...")
        result = run_loventre_meta_engine()
        append_log(result)
        time.sleep(0.1)  # piccolo respiro; regolabile

