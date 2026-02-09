import os
import json
import pandas as pd

# Percorsi
witness_dir = "JSON_IO/LMetrics_v6_witness"
agg_csv_path = "JSON_IO/LMetrics_v6_witness_aggregated.csv"
agg_summary_path = "JSON_IO/LMetrics_v6_witness_summary.csv"

# Caricamento e aggregazione dei witness
all_files = sorted([f for f in os.listdir(witness_dir) if f.endswith(".json")])
witness_list = []

for fname in all_files:
    fpath = os.path.join(witness_dir, fname)
    with open(fpath, "r") as f:
        data = json.load(f)
        data["source_file"] = fname
        witness_list.append(data)

df = pd.DataFrame(witness_list)

# Salvataggio aggregato completo
df.to_csv(agg_csv_path, index=False)
print(f"Aggregazione completata: {len(df)} file uniti")
print(f"CSV → {agg_csv_path}")

# Sintesi SAFE vs BLACKHOLE
decision_count = df["loventre_global_decision"].value_counts()
risk_count = df["risk_class"].value_counts()
summary_table = df.groupby(["loventre_global_decision", "risk_class"]).size().reset_index(name="count")

print("\nConteggio SAFE vs BLACKHOLE:")
print(decision_count)
print("\nConteggio per risk_class:")
print(risk_count)
print("\nTabella aggregata decision x risk_class:")
print(summary_table)

# Salvataggio sintesi
summary_table.to_csv(agg_summary_path, index=False)
print(f"\nSintesi salvata in '{agg_summary_path}'")

