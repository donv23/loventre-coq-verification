#!/usr/bin/env python3
"""
loventre_export_for_coq_batch.py
V60b — converte tutti i witness PACK in LMetrics canonici per Coq,
accettando sia formato:
  { "points": [...] }
sia formato:
  [ {pt1}, {pt2}, ... ]
"""

import json
from datetime import datetime
from pathlib import Path

ROOT = Path(__file__).resolve().parent
WITNESS_PACK = ROOT / "JSON_IO" / "WITNESS_PACK.json"
EXPORT_DIR = (
    Path("/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/JSON_IO")
    / "LMetrics_v3_for_Coq"
)

EXPORT_DIR.mkdir(parents=True, exist_ok=True)

def convert_point_to_lmetrics(p):
    """Converte un punto JSON in record LMetrics compatibile con Coq v3."""
    ts = p.get("timestamp", "")
    return {
        "timestamp": ts,
        "param": p.get("param", 0),
        "factor": p.get("factor", 0),
        "kappa_eff": round(float(p.get("kappa_eff", 0)), 6),
        "entropy_eff": round(float(p.get("entropy_eff", 0)), 6),
        "V0": round(float(p.get("V0", 0)), 6),
        "p_tunnel": round(float(p.get("p_tunnel", 0)), 6),

        # future proof:
        "time_regime": "wild",
        "source": "loventre_engine_v60b_batch",
    }

def export():
    if not WITNESS_PACK.exists():
        print(f"❌ WITNESS_PACK not found: {WITNESS_PACK}")
        return

    data = json.loads(WITNESS_PACK.read_text())

    # ✓ CASE 1: dict with "points"
    if isinstance(data, dict):
        points = data.get("points", [])
    # ✓ CASE 2: list of points
    elif isinstance(data, list):
        points = data
    else:
        print("❌ Unknown witness pack format:", type(data))
        return

    count = 0
    for p in points:
        converted = convert_point_to_lmetrics(p)
        timestamp_safe = converted["timestamp"].replace(":", "-")
        fname = f"lmetrics_for_coq_{timestamp_safe}.json"
        (EXPORT_DIR / fname).write_text(json.dumps(converted, indent=2))
        count += 1

    print("📤 EXPORT COMPLETED (V60b robust)")
    print(f"📁 Directory:", EXPORT_DIR)
    print(f"📦 Files written:", count)

if __name__ == "__main__":
    export()

