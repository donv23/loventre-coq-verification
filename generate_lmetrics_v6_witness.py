import pandas as pd
import json
from pathlib import Path

# Percorsi
input_csv = Path("JSON_IO/LMetrics_v6_aggregated_sorted.csv")
json_output_dir = Path("JSON_IO/LMetrics_v6_witness")
json_output_dir.mkdir(exist_ok=True)

# Caricamento CSV
df = pd.read_csv(input_csv)

# Creazione dei witness v6
for idx, row in df.iterrows():
    filename = json_output_dir / f"witness_v6_{idx+1:03d}.json"
    witness = {
        "kappa_eff": row["kappa_eff"],
        "entropy_eff": row["entropy_eff"] if not pd.isna(row["entropy_eff"]) else None,
        "mass_eff": row["mass_eff"],
        "inertial_idx": row["inertial_idx"],
        "risk_index": row["risk_index"],
        "risk_class": row["risk_class"],
        "loventre_global_decision": row["loventre_global_decision"],
        "loventre_global_color": row["loventre_global_color"],
        "loventre_global_score": row["loventre_global_score"],
        "meta_label": row["meta_label"],
        "source_file": row["source_file"]
    }
    with open(filename, "w") as f:
        json.dump(witness, f, indent=2)

print(f"Generati {len(df)} witness JSON in '{json_output_dir}'")

