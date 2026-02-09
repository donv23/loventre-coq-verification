"""
LOVENTRE ENGINE — CAPTURE WITNESS
Versione 2026-01-12
- Esegue un singolo meta-engine random
- Classifica il punto (SAFE / ACCESS / BH)
- Se ACCESS o BH → salva un witness JSON
- Logga e ritorna l'etichetta
"""

import json
import os
from datetime import datetime

from loventre_meta_engine_random import compute_random_metrics
from loventre_policy_bridge import classify_point

WITNESS_DIR = "JSON_IO/WITNESS"
os.makedirs(WITNESS_DIR, exist_ok=True)

def save_witness(point, label):
    ts = datetime.utcnow().isoformat()
    fname = f"witness_{label}_{ts}.json"
    path = os.path.join(WITNESS_DIR, fname)

    with open(path, "w") as f:
        json.dump(point, f, indent=2)

    return path

if __name__ == "__main__":
    point = compute_random_metrics()
    label = classify_point(point)

    if label in ("ACCESS", "BH"):
        path = save_witness(point, label)
        print(f"📦 SAVED WITNESS [{label}] → {path}")
    else:
        print(f"🙂 SAFE — nessun salvataggio")

    print(f"🔎 CLASSIFIED AS: {label}")

