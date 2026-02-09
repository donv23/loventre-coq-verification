"""
loventre_json_crosscheck_coq.py

Cross-check fra:
  - witness JSON LMetrics (witness_json/*.json) generati dal motore Loventre,
  - file Coq Loventre_LMetrics_JSON_Link.v che mappa lm_id ↔ path JSON.

Obiettivo:
  - Verificare che ogni lm_id_link in Coq abbia un JSON corrispondente.
  - Verificare che ogni JSON abbia un lm_id coerente e sia citato in Coq.
  - Segnalare eventuali mismatch o elementi mancanti.

Questo script non modifica nulla: è solo un controllo di coerenza.
"""

from __future__ import annotations

import re
from pathlib import Path
from typing import Dict, List

from loventre_json_schema import (
    LMetricsWitnessJSON,
    load_witness_json,
)

# ---------------------------------------------------------------------------
# 1. Path principali
# ---------------------------------------------------------------------------

ROOT = Path(__file__).parent
WITNESS_DIR = ROOT / "witness_json"

# Path assoluto del file Coq di link (come usato da te in Coq).
COQ_LINK_FILE = Path(
    "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/"
    "PROGETTO TEOREMA/Loventre_Coq_Modules/Loventre_Coq_Clean/"
    "02_Advanced/Geometry/Loventre_LMetrics_JSON_Link.v"
)


# ---------------------------------------------------------------------------
# 2. Parsing del file Coq per estrarre gli lm_id_link
# ---------------------------------------------------------------------------

def parse_coq_lm_ids(path: Path) -> List[str]:
    """
    Estrae tutti i valori lm_id_link := "..." dal file Coq di link.
    Restituisce una lista di stringhe (potenzialmente con duplicati).
    """
    text = path.read_text(encoding="utf-8")
    pattern = r'lm_id_link\s*:=\s*"([^"]+)"'
    ids = re.findall(pattern, text)
    return ids


# ---------------------------------------------------------------------------
# 3. Caricamento dei witness JSON
# ---------------------------------------------------------------------------

def load_all_witnesses_from_json(directory: Path) -> Dict[str, LMetricsWitnessJSON]:
    """
    Carica tutti i witness JSON da witness_json/*.json e li indicizza per lm_id.
    Se due file hanno lo stesso lm_id, l'ultimo vince ma viene segnalato.
    """
    directory = Path(directory)
    result: Dict[str, LMetricsWitnessJSON] = {}

    if not directory.exists():
        print(f"[WARN] Directory JSON non trovata: {directory}")
        return result

    json_files = sorted(directory.glob("*.json"))
    if not json_files:
        print(f"[WARN] Nessun file .json trovato in {directory}")
        return result

    for path in json_files:
        try:
            w = load_witness_json(path, validate=False)
        except Exception as e:
            print(f"[ERR ] Impossibile caricare {path.name}: {e}")
            continue

        if w.lm_id in result:
            print(
                f"[WARN] lm_id '{w.lm_id}' già visto; il file {path.name} "
                f"sovrascrive il precedente."
            )

        result[w.lm_id] = w

    return result


# ---------------------------------------------------------------------------
# 4. Cross-check principale
# ---------------------------------------------------------------------------

def crosscheck_json_vs_coq() -> None:
    """
    Esegue il confronto fra:
      - lm_id_link elencati in Coq,
      - lm_id presenti nei witness JSON.
    """
    print("=== LOVENTRE JSON ↔ Coq LMetrics Crosscheck ===")
    print(f"Root motore   : {ROOT}")
    print(f"Dir JSON      : {WITNESS_DIR}")
    print(f"File Coq link : {COQ_LINK_FILE}")
    print("")

    if not COQ_LINK_FILE.exists():
        print(f"[ERR ] File Coq di link non trovato: {COQ_LINK_FILE}")
        return

    coq_ids_list = parse_coq_lm_ids(COQ_LINK_FILE)
    coq_ids = sorted(set(coq_ids_list))

    print(f"[INFO] lm_id_link trovati in Coq ({len(coq_ids)} unici):")
    for cid in coq_ids:
        print(f"  - {cid}")
    print("")

    json_witnesses = load_all_witnesses_from_json(WITNESS_DIR)
    json_ids = sorted(json_witnesses.keys())

    print(f"[INFO] lm_id trovati nei JSON ({len(json_ids)} unici):")
    for jid in json_ids:
        print(f"  - {jid}")
    print("")

    # --- 4.1 Coq → JSON: per ogni lm_id_link deve esistere un JSON corrispondente
    print("=== CHECK 1: ogni lm_id_link Coq ha un JSON corrispondente? ===")
    missing_json = []
    for cid in coq_ids:
        if cid not in json_witnesses:
            print(f"[MISS] In Coq ma non in JSON: {cid}")
            missing_json.append(cid)
        else:
            print(f"[OK  ] Coq ↔ JSON presente: {cid}")
    if not missing_json:
        print("[OK  ] Tutti gli lm_id Coq hanno un JSON corrispondente.")
    print("")

    # --- 4.2 JSON → Coq: ogni lm_id JSON deve essere citato in Coq
    print("=== CHECK 2: ogni lm_id JSON è citato in Coq? ===")
    extra_json = []
    for jid in json_ids:
        if jid not in coq_ids:
            print(f"[EXTRA] In JSON ma non in Coq: {jid}")
            extra_json.append(jid)
        else:
            print(f"[OK   ] JSON ↔ Coq presente: {jid}")
    if not extra_json:
        print("[OK  ] Tutti gli lm_id JSON sono citati in Coq.")
    print("")

    # --- 4.3 Coerenza path / convenzione di nome file
    print("=== CHECK 3: convenzione file JSON (witness_json/<lm_id>.json) ===")
    for jid, w in json_witnesses.items():
        expected_name = f"{jid}.json"
        actual_path = WITNESS_DIR / expected_name
        if not actual_path.exists():
            print(
                f"[WARN] Per lm_id={jid}, atteso file {expected_name} "
                f"ma non esiste in {WITNESS_DIR.name}."
            )
        else:
            print(f"[OK  ] lm_id={jid} ↔ file={expected_name}")
    print("")

    print("=== FINE CROSSCHECK ===")


def main() -> None:
    crosscheck_json_vs_coq()


if __name__ == "__main__":
    main()

