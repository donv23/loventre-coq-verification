"""
L14_BLACKHOLE_EXPORT_SUMMARY — V20
==================================

Lancia il monitor e produce un file di sintesi Coq-ready.
"""

import json
import os
from V14_NEXT.l14_blackhole_monitor import run_sequence_v20

EXPORT_DIR = "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/JSON_IO/LMetrics_v3_for_Coq"


def run_export_blackhole_summary_v20(num_steps=100):
    result = run_sequence_v20(num_steps=num_steps)

    if not os.path.exists(EXPORT_DIR):
        os.makedirs(EXPORT_DIR, exist_ok=True)

    fname = "blackhole_non_risalita_summary.json"
    summary_path = os.path.join(EXPORT_DIR, fname)

    # Se esiste un controesempio, salviamolo
    if result["counterexample"] is not None:
        out = {
            "observed_no_recovery_blackhole": False,
            "counterexample": result["counterexample"],
            "tested_runs": result["num_steps"],
        }
    else:
        out = {
            "observed_no_recovery_blackhole": True,
            "counterexample": None,
            "tested_runs": result["num_steps"],
        }

    with open(summary_path, "w") as f:
        json.dump(out, f, indent=2)

    return True

