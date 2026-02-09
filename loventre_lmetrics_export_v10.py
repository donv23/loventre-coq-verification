#!/usr/bin/env python3
import os
import shutil
from datetime import datetime

# Root path absolute - v10 canonical export
ENGINE_ROOT = "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed"
SOURCE_DIR = os.path.join(ENGINE_ROOT, "JSON_IO", "JSON_OUTPUT")

# Destination for Coq canonical ingestion
DEST_BASE = "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/JSON_IO"
DEST_DIR = os.path.join(DEST_BASE, "LMetrics_v10_for_Coq")

def main():
    print("===== LMetrics EXPORT V10 =====")

    # Timestamp
    print(f"[Time] {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}")

    # Create dest folder if missing
    if not os.path.exists(DEST_DIR):
        print(f"[Create] {DEST_DIR}")
        os.makedirs(DEST_DIR, exist_ok=True)

    exported = 0

    # Only match canonical v10 JSONs
    for fname in os.listdir(SOURCE_DIR):
        if fname.lower().endswith(".json") and "_v10" in fname:
            src = os.path.join(SOURCE_DIR, fname)
            dst = os.path.join(DEST_DIR, fname)
            shutil.copyfile(src, dst)
            print(f"[OK] copied {fname}")
            exported += 1

    print(f"[Exported {exported}]")
    print("===== END EXPORT V10 =====")

if __name__ == "__main__":
    main()

