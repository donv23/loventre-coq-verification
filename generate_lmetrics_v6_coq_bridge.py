import json
from pathlib import Path

# Cartella dei witness v6 esportati per Coq
witness_dir = Path("JSON_IO/LMetrics_v6_for_Coq")
coq_dir = Path("Coq_IO/LMetrics_v6")  # cartella di output Coq
coq_dir.mkdir(exist_ok=True, parents=True)

# Funzione per creare un modulo Coq da un JSON
def json_to_coq_module(json_path: Path):
    with open(json_path, "r") as f:
        data = json.load(f)
    module_name = json_path.stem.replace(".json", "")
    coq_file = coq_dir / f"{module_name}.v"
    
    with open(coq_file, "w") as f:
        f.write(f"Module {module_name}.\n\n")
        for key, value in data.items():
            if isinstance(value, str):
                f.write(f"Definition {key} := \"{value}\".\n")
            else:
                f.write(f"Definition {key} := {value}.\n")
        f.write("\nEnd {module_name}.\n")
    print(f"✔ Modulo Coq generato: {coq_file}")

# Loop su tutti i file JSON
for json_file in sorted(witness_dir.glob("*.json")):
    json_to_coq_module(json_file)

print("\nTutti i witness v6 sono stati convertiti in moduli Coq nella cartella 'Coq_IO/LMetrics_v6'.")

