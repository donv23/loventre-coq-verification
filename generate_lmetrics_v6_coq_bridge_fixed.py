import json
from pathlib import Path

# Cartella dei witness JSON generati
witness_json_dir = Path("JSON_IO/LMetrics_v6_for_Coq")
coq_output_dir = Path("Coq_IO/LMetrics_v6")
coq_output_dir.mkdir(exist_ok=True)

# Lista dei file JSON ordinati
json_files = sorted(witness_json_dir.glob("lmetrics_for_coq_witness_*.json"))

for idx, json_file in enumerate(json_files, start=1):
    with open(json_file, "r") as f:
        data = json.load(f)

    # Nome del modulo Coq
    coq_filename = coq_output_dir / f"witness_v6_{idx:03}.v"

    with open(coq_filename, "w") as coq_file:
        # Header modulo Coq con import corretto
        coq_file.write("From LMetrics_v6 Require Import LMetrics_v6_types.\n")
        coq_file.write(f"Module witness_v6_{idx:03}.\n\n")

        # Scrittura delle metriche come definizioni Coq
        for key, value in data.items():
            if isinstance(value, str):
                coq_file.write(f'Definition {key} := "{value}".\n')
            elif isinstance(value, int):
                coq_file.write(f"Definition {key} := {value}.\n")
            elif isinstance(value, float):
                coq_file.write(f"Definition {key} := {value}.\n")
            elif isinstance(value, bool):
                coq_file.write(f"Definition {key} := {str(value).lower()}.\n")
            else:
                coq_file.write(f"(* {key}: {value} non supportato direttamente *)\n")

        coq_file.write(f"\nEnd witness_v6_{idx:03}.\n")

    print(f"✔ Modulo Coq generato: {coq_filename.name}")

