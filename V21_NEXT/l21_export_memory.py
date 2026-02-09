"""
V21 NEXT — EXPORT MEMORY SUMMARY
Produce un sommario leggibile della memoria recente.
"""

import json
import os

from .l21_memory_core import tail_memory, ensure_memory_ready
from .l21_trend_classifier import classify_trend

SUMMARY_FILE = os.path.join("V21_MEMORY", "v21_summary.json")

def compute_summary(window=50):
    recent = tail_memory(window)
    safe = sum(1 for r in recent if r.get("decision") == "SAFE")
    acc = sum(1 for r in recent if r.get("decision") in ("SAFE_ACCESSIBLE", "P_ACC", "ACCESSIBLE"))
    bh  = sum(1 for r in recent if r.get("is_blackhole"))
    trend = classify_trend(window=window)

    return {
        "total_observed": len(recent),
        "safe_count": safe,
        "accessible_count": acc,
        "blackhole_count": bh,
        "trend": trend,
    }

def export_summary(window=50):
    ensure_memory_ready()
    summary = compute_summary(window)
    with open(SUMMARY_FILE, "w") as f:
        json.dump(summary, f, indent=2)
    return SUMMARY_FILE

