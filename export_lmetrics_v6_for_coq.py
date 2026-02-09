import os
import json
import shutil

# Cartelle
witness_dir = "JSON_IO/LMetrics_v6_witness"
coq_bridge_dir = "JSON_IO/LMetrics_v6_for_Coq"

# Creazione cartella di destinazione
os.makedirs(coq_bridge_dir, exist_ok=True)

# Copia e normalizzazione dei JSON per Coq
all_files = sorted([f for f in os.listdir(witness_dir) if f.endswith(".json")])
for fname in all_files:
    src_path = os.path.join(witness_dir, fname)
    dst_path = os.path.join(coq_bridge_dir, fname)

    with open(src_path, "r") as f:
        data = json.load(f)
    
    # Normalizzazione: assicurarsi che NaN → null
    for key in data:
        if data[key] is None:
            data[key] = None

    # Salvataggio nel bridge Coq
    with open(dst_path, "w") as f:
        json.dump(data, f, indent=2)

print(f"Tutti i {len(all_files)} witness esportati in '{coq_bridge_dir}'")

