"""
L14_HISTORY_CORE — V17
======================

Memoria minima persistente per il Loventre Engine.

- Registra ogni snapshot V14 in history_v17.json
- Mantiene contatori aggregati
- Ignora valori mancanti
"""

import json
import os
from datetime import datetime

HISTORY_DIR = "V14_HISTORY"
HISTORY_FILE = "history_v17.json"


def _ensure_history_file():
    if not os.path.exists(HISTORY_DIR):
        os.makedirs(HISTORY_DIR, exist_ok=True)
    filepath = os.path.join(HISTORY_DIR, HISTORY_FILE)
    if not os.path.exists(filepath):
        with open(filepath, "w") as f:
            json.dump([], f)
    return filepath


def _load_history():
    filepath = _ensure_history_file()
    with open(filepath, "r") as f:
        try:
            data = json.load(f)
            if isinstance(data, list):
                return data
        except Exception:
            pass
    return []


def _save_history(history_list):
    filepath = _ensure_history_file()
    with open(filepath, "w") as f:
        json.dump(history_list, f, indent=2)


def record_event(snapshot_v14):
    """
    Registra un evento V14.
    Lo snapshot deve già contenere timestamp/version/hash.
    """
    if not isinstance(snapshot_v14, dict):
        return False

    history = _load_history()
    history.append(snapshot_v14)
    _save_history(history)
    return True


def compute_history_summary():
    """
    Calcola statistiche aggregati:
    - totale
    - ratio BH / SAFE / PACC
    """
    history = _load_history()
    total = len(history)
    if total == 0:
        return {
            "total": 0,
            "blackhole": 0,
            "safe": 0,
            "safe_accessible": 0,
            "ratio_blackhole": None,
        }

    blackhole = sum(1 for h in history if h.get("state") == "BLACKHOLE")
    safe = sum(1 for h in history if h.get("state") == "SAFE")
    pacc = sum(1 for h in history if h.get("state") == "SAFE_ACCESSIBLE")

    return {
        "total": total,
        "blackhole": blackhole,
        "safe": safe,
        "safe_accessible": pacc,
        "ratio_blackhole": blackhole / total,
    }

