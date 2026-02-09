import pandas as pd

# Percorso CSV ordinato
csv_path = "JSON_IO/LMetrics_v6_aggregated_sorted.csv"

# Caricamento CSV
df = pd.read_csv(csv_path)

# Visualizzazione prime righe
print("Prime righe del CSV ordinato:")
print(df.head(), "\n")

# Conteggio decisioni SAFE vs BLACKHOLE
decision_counts = df['loventre_global_decision'].value_counts()
print("Conteggio SAFE vs BLACKHOLE:")
print(decision_counts, "\n")

# Conteggio per risk_class
risk_counts = df['risk_class'].value_counts()
print("Conteggio per risk_class:")
print(risk_counts, "\n")

# Aggregazione combinata: decision x risk_class
agg_table = df.groupby(['loventre_global_decision','risk_class']).size().reset_index(name='count')
print("Tabella aggregata decision x risk_class:")
print(agg_table, "\n")

# Salvataggio sintesi in CSV
summary_csv_path = "JSON_IO/LMetrics_v6_summary.csv"
agg_table.to_csv(summary_csv_path, index=False)
print(f"Sintesi salvata in '{summary_csv_path}'")

