#!/usr/bin/env python3
"""
Loventre CLI Witness Export (Canvas 23)

Usage:
python3 loventre_cli_export.py input.json output.loventrew
"""

import sys
import json
import hashlib

from json_bridge import LoventreJSONBridge
from loventre_meta_engine import loventre_meta_engine
from loventre_policy_export import loventre_policy_export


def load_json(fname):
    with open(fname, "r") as f:
        return json.load(f)


def format_witness(export_dict):
    """
    Transform dict into structured witness text.
    """
    lines = [
        "WITNESS",
        f"TYPE={export_dict['witness_type']}",
        f"DECISION={export_dict['decision']}",
        f"SCORE={export_dict['score']}",
        f"COLOR={export_dict['color']}",
        f"FINGERPRINT={export_dict['fingerprint']}",
    ]
    return "\n".join(lines) + "\n"


def main():
    if len(sys.argv) != 3:
        print("Usage: python3 loventre_cli_export.py input.json output.loventrew")
        sys.exit(1)

    input_json = sys.argv[1]
    output_w = sys.argv[2]

    data = load_json(input_json)

    meta = loventre_meta_engine(LoventreJSONBridge.json_to_metrics(data))
    exp = loventre_policy_export(meta)

    txt = format_witness(exp)

    with open(output_w, "w") as f:
        f.write(txt)

    print(f"[OK] Witness exported to {output_w}")


if __name__ == "__main__":
    main()

