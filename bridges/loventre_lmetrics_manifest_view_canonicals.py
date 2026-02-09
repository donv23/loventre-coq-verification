#!/usr/bin/env python3
"""
loventre_lmetrics_manifest_view_canonicals.py

Mostra una vista compatta dei profili LMetrics "canonici" (scala 0–1)
dal manifest LOVENTRE_LMETRICS_MANIFEST_v3.json.

- Filtra scale_hint == "0_1".
- Mostra: seed_id, role_hint, phase_guess, risk_index, chi_compactness,
           horizon_flag, black_hole_hint.

Non modifica nulla.
"""

import json
from pathlib import Path
from typing import Any, Dict, List


def load_manifest(path: Path) -> Dict[str, Any]:
    if not path.is_file():
        raise SystemExit(f"[ERROR] Manifest non trovato: {path}")
    text = path.read_text(encoding="utf-8")
    return json.loads(text)


def main() -> None:
    path = Path("LOVENTRE_LMETRICS_MANIFEST_v3.json")
    manifest = load_manifest(path)
    entries: List[Dict[str, Any]] = manifest.get("entries", [])

    canonicals = [e for e in entries if e.get("scale_hint") == "0_1"]

    if not canonicals:
        print("[INFO] Nessun profilo canonico (0_1) trovato.")
        return

    print("=== LOVENTRE LMetrics Canonical Profiles (scale 0–1) ===")
    print(f"{'seed_id':18} {'role_hint':20} {'phase':20} {'risk':6} {'chi':6} {'horizon':8} {'BH_hint':8}")
    print("-" * 90)

    for e in canonicals:
        print(
            f"{e.get('seed_id','<unk>'):18} "
            f"{e.get('role_hint','<unk>'):20} "
            f"{e.get('phase_guess','<unk>'):20} "
            f"{e.get('risk_index',0):<6.2f} "
            f"{e.get('chi_compactness',0):<6.2f} "
            f"{str(e.get('horizon_flag',False)):8} "
            f"{str(e.get('black_hole_hint',False)):8}"
        )


if __name__ == "__main__":
    main()

