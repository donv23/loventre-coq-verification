"""
loventre_meta_portfolio_lab.py
---------------------------------
Demo riepilogativa ("meta-portfolio") del Loventre Engine.
Raccoglie seed_grid + famiglie critiche SAT/TSP e mostra strategie sintetiche.
"""

from loventre_instance_analysis import analyze_instance, suggest_strategy
from loventre_metrics_bus import ensure_loventre_keys

print("===================================================================")
print("=== LOVENTRE META-PORTFOLIO LAB                                ===")
print("===================================================================\n")

seeds = [(p, f) for p in [1, 2, 3] for f in [1, 2, 3]]
families = ["SAT_crit16", "TSP_crit28"]

rows = []

# Analisi dei seed base
for p, f in seeds:
    label = f"seed_{p}_{f}"
    m = analyze_instance(label)
    m = ensure_loventre_keys(m)
    strat = suggest_strategy(m)
    rows.append((label, m["risk_class"], m["meta_label"], strat))

# Analisi famiglie critiche
for fam in families:
    m = analyze_instance(fam)
    m = ensure_loventre_keys(m)
    strat = suggest_strategy(m)
    rows.append((fam, m["risk_class"], m["meta_label"], strat))

# Output
print(f"{'Instance':15} {'RiskClass':20} {'MetaLabel':25} Strategy")
print("-" * 80)
for name, risk, meta, strat in rows:
    print(f"{name:15} {risk:20} {meta:25} {strat}")
print("\n[ OK ] loventre_meta_portfolio_lab.py")

