"""
L14_EXPORT_MULTI — V16
======================

Produce un export aggregato da lista canonica.
"""

import json
import os
from V14_NEXT.l14_multi_input import compute_multi_input_stats

OUTPUT_DIR = "V14_JSON_CANON"

def run_export_multi_v16():
    raw_list = [0.2, 0.5, 0.9]

    stats = compute_multi_input_stats(raw_list)

    fname = "v14_multi_case.json"
    if not os.path.exists(OUTPUT_DIR):
        os.makedirs(OUTPUT_DIR, exist_ok=True)

    with open(os.path.join(OUTPUT_DIR, fname), "w") as f:
        json.dump(stats, f, indent=2)

    return True

