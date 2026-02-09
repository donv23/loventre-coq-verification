import json
import os

BASE = "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/JSON_IO/LMetrics_v3_for_Coq"

def load_signature(fname):
    with open(os.path.join(BASE, fname), "r") as f:
        m = json.load(f)
    return (
        m["time_regime"],
        m["horizon_flag"],
        m["meta_label"]
    )

print("\n[Axis C — Deep Computational Re-encoding Invariance Test]\n")

sat_sig = load_signature("lmetrics_for_coq_m_SATcrit16_v3.json")
csp_sig = load_signature("lmetrics_for_coq_m_CSPcrit16_v3.json")

print("SAT_crit16 signature :", sat_sig)
print("CSP_crit16 signature :", csp_sig)

print("\n[RESULT]")

if sat_sig == csp_sig:
    print("✔ Invarianza confermata")
    print("→ Il regime è indipendente dal formalismo computazionale")
else:
    print("✘ Invarianza VIOLATA")
    print("→ La ricodifica altera il regime (STOP)")

