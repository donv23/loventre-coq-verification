#!/usr/bin/env python3
"""
Loventre v3 – Coq Witness Export from JSON

Scopo:
  - Chiamare loventre_metrics_cli_coq_bridge.py per i quattro witness
    principali (m_P, m_Pacc, m_NP_TSP, m_NP_SAT).
  - Estrarre dallo stdout gli snippet Coq "Definition m_* : LMetrics := ..."
    auto-generati dal bridge.
  - Scriverli in un unico file:

        LOVENTRE_V3_Main_Witness_From_JSON.v

    nella root del motore, pronto da aprire con nano e copiare
    dentro i moduli Coq (es. Loventre_LMetrics_JSON_Witness.v).

Nota:
  - Questo script NON modifica nessun file Coq.
  - Il file .v generato è solo un contenitore comodo degli snippet.
"""

import pathlib
import subprocess
import sys
from typing import List, Tuple


ROOT = pathlib.Path(__file__).resolve().parent
OUTFILE = ROOT / "LOVENTRE_V3_Main_Witness_From_JSON.v"

# metrics_json, def_name, ruolo logico
CASES: List[Tuple[str, str, str]] = [
    ("metrics_seed11_cli_demo.json", "m_seed11_cli_demo", "m_P (P_like)"),
    (
        "metrics_seed_grid_demo_global.json",
        "m_seed_grid_demo",
        "m_Pacc (P_like_accessible)",
    ),
    (
        "metrics_TSP_crit28_demo.json",
        "m_TSPcrit28_cli_demo",
        "m_NP_TSP (NP_like_crit TSP_crit28)",
    ),
    (
        "metrics_SAT_crit16_demo.json",
        "m_SATcrit16_cli_demo",
        "m_NP_SAT (NP_like_crit SAT_crit16)",
    ),
]


def run_bridge(metrics_name: str, def_name: str) -> str:
    """
    Esegue loventre_metrics_cli_coq_bridge.py per una coppia
    (metrics_json, def_name) e restituisce l'intero stdout.
    """
    cmd = [
        sys.executable,
        "loventre_metrics_cli_coq_bridge.py",
        "--metrics-json",
        metrics_name,
        "--def-name",
        def_name,
    ]
    result = subprocess.run(
        cmd,
        cwd=ROOT,
        check=True,
        capture_output=True,
        text=True,
    )
    return result.stdout


def extract_snippet(output: str) -> str:
    """
    Estrae dal testo l'unico snippet Coq del tipo:

      (* Auto-generated from CLI for definition ... *)
      Definition m_... : LMetrics := ...
      ...
      (* End of auto-generated snippet. *)

    Se non trova i marker, solleva un'eccezione.
    """
    start_token = "(* Auto-generated from CLI for definition"
    end_token = "(* End of auto-generated snippet. *)"

    start_idx = output.find(start_token)
    if start_idx == -1:
        raise RuntimeError("Marker di inizio snippet non trovato nello stdout.")

    end_idx = output.find(end_token, start_idx)
    if end_idx == -1:
        raise RuntimeError("Marker di fine snippet non trovato nello stdout.")

    end_idx = end_idx + len(end_token)
    snippet = output[start_idx:end_idx]
    return snippet.strip() + "\n\n"


def main() -> None:
    print("============================================================")
    print(" Loventre v3 – Export Coq Witness From JSON")
    print("============================================================")
    print(f"Root motore: {ROOT}")
    print(f"File di output: {OUTFILE}")
    print("")

    snippets: List[str] = []

    for metrics_name, def_name, role_descr in CASES:
        print(f"[RUN ] {metrics_name} → {def_name} ({role_descr})")
        stdout = run_bridge(metrics_name, def_name)
        snippet = extract_snippet(stdout)
        snippets.append(f"(* {role_descr} – from {metrics_name} *)\n{snippet}")
        print(f"[ OK ] Estratto snippet per {def_name}")
        print("")

    header = """(*
**********************************************************************
* LOVENTRE_V3_Main_Witness_From_JSON.v                               *
**********************************************************************

File AUTO-GENERATO da:

  python3 loventre_v3_main_witness_coq_export.py

Root motore Python:
  /Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/
  ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed

Scopo:
  - Contenere in un unico posto gli snippet Coq:

      Definition m_seed11_cli_demo : LMetrics := ...
      Definition m_seed_grid_demo  : LMetrics := ...
      Definition m_TSPcrit28_cli_demo : LMetrics := ...
      Definition m_SATcrit16_cli_demo : LMetrics := ...

    generati a partire dai JSON:

      metrics_seed11_cli_demo.json
      metrics_seed_grid_demo_global.json
      metrics_TSP_crit28_demo.json
      metrics_SAT_crit16_demo.json

  - Questo file NON è pensato per essere compilato così com'è.
    Va usato come sorgente da cui copiare/incollare le definizioni
    dentro i moduli Coq appropriati (es. Loventre_LMetrics_JSON_Witness.v).

ATTENZIONE:
  - NON modificare questo file a mano.
  - Se servono aggiornamenti, rigenerarlo eseguendo di nuovo lo script
        python3 loventre_v3_main_witness_coq_export.py
**********************************************************************
*)

"""

    content = header + "\n\n".join(snippets)

    OUTFILE.write_text(content, encoding="utf-8")

    print("[DONE] File Coq generato:")
    print(f"       {OUTFILE}")
    print("")
    print("Ora puoi aprirlo con, ad esempio:")
    print(f'  nano "{OUTFILE.name}"')
    print("e copiare gli snippet nei moduli Coq (senza doverli ricostruire a mano).")


if __name__ == "__main__":
    main()

