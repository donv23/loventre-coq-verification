"""
V22 — Export Attractor Summary
Scrive una fotografia dei movimenti dinamici recenti.
"""

import json
import os

from .l22_transition_counter import compute_transition_counts
from .l22_attractor import classify_attractor

ATTRACTOR_FILE = os.path.join("V22_MEMORY", "v22_attractor_summary.json")

def export_attractor_summary(window=100):
    counts = compute_transition_counts(window)
    attractor = classify_attractor(window)

    summary = {
        "window": window,
        "transition_counts": counts,
        "attractor": attractor,
    }

    os.makedirs("V22_MEMORY", exist_ok=True)
    with open(ATTRACTOR_FILE, "w") as f:
        json.dump(summary, f, indent=2)

    return ATTRACTOR_FILE

