import json
import csv
from pathlib import Path

# Percorso cartella dei JSON
json_folder = Path("JSON_IO/LMetrics_v6_cli_bridge")
output_json_file = Path("JSON_IO/LMetrics_v6_aggregated.json")
output_csv_file = Path("JSON_IO/LMetrics_v6_aggregated.csv")

# Lista di tutti i file JSON
json_files = sorted(json_folder.glob("*.json"))

# Lista per accumulare tutti i dati
all_data = []

for jf in json_files:
    with open(jf, "r") as f:
        data = json.load(f)
        # Aggiungi il nome del file per tracciabilità
        data["source_file"] = jf.name
        all_data.append(data)

# Salva JSON aggregato
with open(output_json_file, "w") as f:
    json.dump(all_data, f, indent=2)

# Salva CSV
if all_data:
    fieldnames = list(all_data[0].keys())
    with open(output_csv_file, "w", newline="") as f:
        writer = csv.DictWriter(f, fieldnames=fieldnames)
        writer.writeheader()
        writer.writerows(all_data)

print(f"Aggregazione completata: {len(all_data)} file uniti")
print(f"JSON → {output_json_file}")
print(f"CSV → {output_csv_file}")

