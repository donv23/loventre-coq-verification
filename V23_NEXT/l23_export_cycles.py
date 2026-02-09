"""
V23 — Export Cycles Summary
Sintesi completa del comportamento ciclico attuale.
"""

import json
import os

from V23_NEXT.l23_cycle_detector import detect_cycle
from V23_NEXT.l23_season_classifier import classify_season
from V22_NEXT.l22_attractor import classify_attractor
from V22_NEXT.l22_transition_counter import compute_transition_counts

CYCLE_FILE = os.path.join("V23_MEMORY", "v23_cycles_summary.json")

def export_cycle_summary(window=100):
    os.makedirs("V23_MEMORY", exist_ok=True)

    summary = {
        "window": window,
        "cycle_state": detect_cycle(window),
        "season": classify_season(window),
        "attractor": classify_attractor(window),
        "transition_counts": compute_transition_counts(window),
    }

    with open(CYCLE_FILE, "w") as f:
        json.dump(summary, f, indent=2)

    return CYCLE_FILE

