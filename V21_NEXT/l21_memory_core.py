"""
V21 NEXT — MEMORY CORE
Registra in V21_MEMORY/ uno stream append-only di eventi
senza mai modificare V13/V14.
"""

import json
import os
from datetime import datetime

MEMORY_DIR = "V21_MEMORY"
MEMORY_FILE = os.path.join(MEMORY_DIR, "v21_memory_log.jsonl")

def ensure_memory_ready():
    """Garantisce che la directory e il file esistano."""
    os.makedirs(MEMORY_DIR, exist_ok=True)
    if not os.path.exists(MEMORY_FILE):
        with open(MEMORY_FILE, "w") as f:
            pass
    return MEMORY_FILE

def append_memory_snapshot(state_dict):
    """
    Aggiunge una riga JSON allo stream.
    state_dict deve includere:
      raw_value, decision_state, entropy, blackhole_flag
    """
    ensure_memory_ready()
    record = {
        "timestamp": datetime.utcnow().isoformat() + "Z",
        "raw_value": state_dict.get("raw_value"),
        "decision": state_dict.get("decision_state"),
        "entropy": state_dict.get("entropy"),
        "is_blackhole": state_dict.get("is_blackhole", False)
    }
    with open(MEMORY_FILE, "a") as f:
        f.write(json.dumps(record) + "\n")
    return record

def tail_memory(n=20):
    """Restituisce le ultime n righe come dict."""
    ensure_memory_ready()
    lines = []
    try:
        with open(MEMORY_FILE, "r") as f:
            for line in f:
                line = line.strip()
                if line:
                    lines.append(json.loads(line))
    except FileNotFoundError:
        return []
    return lines[-n:]

