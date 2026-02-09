"""
V29_NEXT/l29_export_resonance.py
Esporta il profilo di rischio V29 in JSON.
"""

import json
from pathlib import Path
from datetime import datetime

from V29_NEXT.l29_risk_resonance import compute_risk_resonance


def _now_ts():
    return datetime.utcnow().replace(microsecond=0).isoformat() + "Z"


def run_export_resonance_v29(history=None):
    """
    history = lista di float ∈ [0,1]
    ritorna uno snapshot + scrive JSON
    """
    if history is None:
        history = [0.1, 0.3, 0.15, 0.22]  # default demo

    label = compute_risk_resonance(history)

    snap = {
        "version": "V29",
        "module": "l29_export_resonance",
        "timestamp": _now_ts(),
        "history": history,
        "risk_resonance_class": label,
        "flags": {
            "is_calm": label == "CALM",
            "is_pulsed": label == "PULSED",
            "is_resonant": label == "RESONANT",
        }
    }

    out_dir = Path("V29_JSON_DEMO")
    out_dir.mkdir(parents=True, exist_ok=True)

    fname = out_dir / f"v29_resonance_{label.lower()}.json"
    with fname.open("w", encoding="utf-8") as f:
        json.dump(snap, f, indent=2)

    return snap


if __name__ == "__main__":
    print(json.dumps(run_export_resonance_v29(), indent=2))

