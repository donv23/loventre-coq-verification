import pandas as pd
import matplotlib.pyplot as plt

# Percorso del CSV di sintesi
summary_csv = "JSON_IO/LMetrics_v6_summary.csv"

# Caricamento
df = pd.read_csv(summary_csv)

# Pivot per facilitare il plotting
pivot_df = df.pivot(index="risk_class", columns="loventre_global_decision", values="count").fillna(0)

# Creazione del grafico a barre
pivot_df.plot(kind="bar", stacked=True, figsize=(8,6), color=["red", "green"])

plt.title("Distribuzione SAFE vs BLACKHOLE per risk_class (LMetrics v6)")
plt.ylabel("Conteggio")
plt.xlabel("Risk Class")
plt.xticks(rotation=0)
plt.legend(title="Decisione Globale")
plt.tight_layout()

# Salvataggio del grafico
plt.savefig("JSON_IO/LMetrics_v6_summary_plot.png")
plt.show()

print("Grafico generato e salvato come 'JSON_IO/LMetrics_v6_summary_plot.png'")

