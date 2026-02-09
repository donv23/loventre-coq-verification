"""
V27_NEXT/l27_export_self_tuning.py
Esporta decisioni di self-tuning V27 in JSON canonici.
"""

import json
from pathlib import Path
from datetime import datetime

from V27_NEXT.l27_self_tuning import compute_self_tuning


def _now_ts():
    """Timestamp ISO pulito."""
    return datetime.utcnow().replace(microsecond=0).isoformat() + "Z"


def run_export_self_tuning(raw: float = 0.45):
    """
    1) Calcola self-tuning
    2) Costruisce snapshot JSON
    3) Salva in V27_JSON_DEMO
    4) Ritorna il dict
    """
    out = compute_self_tuning(raw)

    snap = {
        "version": "V27",
        "module": "l27_export_self_tuning",
        "timestamp": _now_ts(),
        "input_raw": raw,
        "self_tuning_outcome": out,
        "flags": {
            "auto_steady": out == "STEADY",
            "auto_adapt": out == "ADAPT",
            "auto_retune": out == "RETUNE",
        }
    }

    # path in repo
    out_dir = Path("V27_JSON_DEMO")
    out_dir.mkdir(parents=True, exist_ok=True)

    fname = out_dir / f"v27_self_tuning_{snap['self_tuning_outcome'].lower()}.json"

    with fname.open("w", encoding="utf-8") as f:
        json.dump(snap, f, indent=2)

    return snap


if __name__ == "__main__":
    print(json.dumps(run_export_self_tuning(0.45), indent=2))

