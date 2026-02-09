#!/usr/bin/env python3
"""
loventre_lmetrics_manifest_view_legacy.py

Vista compatta dei profili LMetrics legacy (scala 0–10) dal manifest
LOVENTRE_LMETRICS_MANIFEST_v3.json.

- Filtra scale_hint == "0_10_legacy".
- Mostra: path, seed_id, risk_index, chi_compactness, horizon_flag,
          risk_class, black_hole_hint.

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

    legacy = [e for e in entries if e.get("scale_hint") == "0_10_legacy"]

    if not legacy:
        print("[INFO] Nessun profilo legacy (0_10_legacy) trovato.")
        return

    print("=== LOVENTRE LMetrics Legacy Profiles (scale 0–10) ===")
    print(
        f"{'risk':6} {'chi':6} {'horizon':8} {'BH_hint':8} "
        f"{'risk_cls':18} {'seed_id':18} path"
    )
    print("-" * 100)

    for e in legacy:
        risk = float(e.get("risk_index", 0.0))
        chi = float(e.get("chi_compactness", 0.0))
        horizon = str(e.get("horizon_flag", False))
        bh_hint = str(e.get("black_hole_hint", False))
        risk_cls = str(e.get("risk_class", ""))
        seed_id = str(e.get("seed_id", "<unknown>"))
        path_str = str(e.get("path", ""))

        print(
            f"{risk:6.2f} {chi:6.2f} {horizon:8} {bh_hint:8} "
            f"{risk_cls:18} {seed_id:18} {path_str}"
        )


if __name__ == "__main__":
    main()

