"""
Loventre v5.2 — Informational Profile Demo
(Orthogonal to Coq — zero interference)

OBIETTIVO:
- Caricare 6 witness canonici
- Stampare Φ(M) = informational_potential
- Ordinarli per profilazione

NOTE:
- Non modifica il bus
- Non modifica JSON
- Non tocca Policy
"""

import json
from loventre_informational_tools import informational_print_table

WITNESS_FILES = [
    "metrics_seed11_cli_demo.json",
    "metrics_seed_grid_demo_global.json",
    "metrics_TSP_crit28_demo.json",
    "metrics_SAT_crit16_demo.json",
    "metrics_2SAT_easy_demo.json",
    "metrics_2SAT_crit_demo.json",
]

def load_metrics(fname):
    with open(f"witness_json/{fname}", "r") as f:
        return json.load(f)

def main():
    named_metrics = []
    for fname in WITNESS_FILES:
        M = load_metrics(fname)
        named_metrics.append((fname, M))
    informational_print_table(named_metrics)

if __name__ == "__main__":
    main()

