"""
Loventre Unified Pipeline (Canvas 28 CLEAN)
"""

import sys
import json

from json_bridge import LoventreJSONBridge
from loventre_meta_engine import loventre_meta_engine
from loventre_policy_export import loventre_policy_export


def loventre_pipeline(input_json: dict) -> dict:
    """
    Input: raw dict
    Output: export-ready witness dict
    """
    lmetrics = LoventreJSONBridge.json_to_metrics(input_json)
    meta = loventre_meta_engine(lmetrics)
    exported = loventre_policy_export(meta)
    return exported


def main():
    if len(sys.argv) != 3:
        print("Usage: python3 loventre_pipeline.py input.json output.loventrew")
        sys.exit(1)

    infile = sys.argv[1]
    outfile = sys.argv[2]

    try:
        with open(infile, "r") as f:
            raw = json.load(f)
    except Exception as e:
        print(f"[ERROR] Cannot load JSON: {e}")
        sys.exit(1)

    exported = loventre_pipeline(raw)

    lines = [
        "WITNESS",
        f"TYPE={exported['witness_type']}",
        f"DECISION={exported['decision']}",
        f"LMETRICS_TYPE={exported['LMetrics_type']}",
        f"SCORE={exported['score']}",
        f"COLOR={exported['color']}",
        f"FINGERPRINT={exported['fingerprint']}",
    ]

    with open(outfile, "w") as f:
        for line in lines:
            f.write(line + "\n")

    print(f"[OK] Pipeline export done → {outfile}")


if __name__ == "__main__":
    main()

