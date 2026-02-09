import json
from pathlib import Path

JSON_PATH = Path("/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/JSON_IO/LMetrics_v2/loventre_lmetrics_witness_v16.json")
OUT_V = Path("/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/PROGETTO TEOREMA/Loventre_Coq_Modules/Loventre_Coq_v11/04_Main_v11/Loventre_JSON_Witness_v17.v")

data = json.loads(JSON_PATH.read_text())

header = """(** Loventre_JSON_Witness_v17.v — import statico dal JSON v16 **)

Require Import Loventre_v11_Core.Loventre_LMetrics_v11.

Module Loventre_JSON_Witness_v17.

Import Loventre_LMetrics_v11.
"""

body = ""

for name, info in data.items():
    risk = int(info["risk_level"])
    body += f"Definition {name}_v17 : LMetrics := mkMetrics {risk}.\n"

footer = """

End Loventre_JSON_Witness_v17.
"""

OUT_V.write_text(header + body + footer)
print(f"GENERATED → {OUT_V}")

