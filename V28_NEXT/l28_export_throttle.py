"""
V28_NEXT/l28_export_throttle.py
Esporta decisione di adaptive throttle V28 in JSON.
"""

import json
from pathlib import Path
from datetime import datetime

from V28_NEXT.l28_adaptive_throttle import compute_adaptive_throttle


def _now_ts():
    """Timestamp ISO compatto."""
    return datetime.utcnow().replace(microsecond=0).isoformat() + "Z"


def run_export_throttle_v28(risk: float = 0.5):
    """
    1) Calcola adaptive throttle
    2) Costruisce snapshot JSON
    3) Salva in V28_JSON_DEMO
    4) Ritorna il dict
    """
    out = compute_adaptive_throttle(risk)

    snap = {
        "version": "V28",
        "module": "l28_export_throttle",
        "timestamp": _now_ts(),
        "input_risk": risk,
        "adaptive_throttle_decision": out,
        "flags": {
            "is_boost": out == "BOOST",
            "is_hold": out == "HOLD",
            "is_reduce": out == "REDUCE",
        }
    }

    out_dir = Path("V28_JSON_DEMO")
    out_dir.mkdir(parents=True, exist_ok=True)

    fname = out_dir / f"v28_throttle_{out.lower()}.json"
    with fname.open("w", encoding="utf-8") as f:
        json.dump(snap, f, indent=2)

    return snap


if __name__ == "__main__":
    print(json.dumps(run_export_throttle_v28(0.5), indent=2))

