from __future__ import annotations

import sys
from pathlib import Path

# Aggiungiamo la root del progetto al sys.path
ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from loventre_metrics_bus import (
    new_metrics_bus,
    validate_metrics_bus,
    METRICS_KEYS_CORE,
)


def main() -> None:
    bus = new_metrics_bus()
    print("[INFO] new_metrics_bus creato.")
    print(f"[INFO] Numero di chiavi: {len(bus)}")

    # Controllo che tutte le chiavi core siano presenti
    try:
        validate_metrics_bus(bus)
    except ValueError as e:
        print(f"[FAIL] validate_metrics_bus ha rilevato un problema: {e}")
        return

    missing = [k for k in METRICS_KEYS_CORE if k not in bus]
    if missing:
        print(f"[FAIL] Chiavi core mancanti: {missing}")
    else:
        print("[OK] Tutte le chiavi core presenti nel bus.")

    print("[SNAPSHOT] Valori di default:")
    for k in sorted(bus.keys()):
        print(f"  {k}: {bus[k]}")


if __name__ == "__main__":
    main()

