#!/usr/bin/env python3
import json
import os

# ===============================================================
# LOVENTRE INFORMATIONAL ENHANCED PROFILE (v5.3-TER + Gravity)
# ===============================================================

WITNESS_ROOT = os.path.join(
    "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs",
    "ALGORITIMIA",
    "LOVENTRE_ENGINE_CLEAN",
    "loventre_engine_clean_seed",
    "witness_json"
)

FILES = [
    "m_seed11_cli_demo.json",
    "m_seed_grid_demo.json",
    "m_TSPcrit28_cli_demo.json",
    "m_SATcrit16_cli_demo.json",
    "m_2SAT_easy_demo.json",
    "m_2SAT_crit_demo.json"
]

def safe_get(d, key):
    return d[key] if key in d else None

def load_metrics(fname):
    full = os.path.join(WITNESS_ROOT, fname)
    with open(full, "r") as f:
        return json.load(f)

def compute_info(metrics):
    kappa = safe_get(metrics, "kappa_eff")
    entropy = safe_get(metrics, "entropy_eff")
    V0 = safe_get(metrics, "V0")

    infoP = None
    inertia = None
    gravity = None

    if kappa is not None and entropy is not None:
        infoP = 0.5 * (kappa + entropy)

    if V0 is not None and infoP is not None:
        inertia = abs(V0 - infoP)
        denom = 1.0 + kappa + entropy
        gravity = inertia / denom

    return kappa, entropy, V0, infoP, inertia, gravity


def classify(V0, infoP, inertia):
    if V0 is None or infoP is None or inertia is None:
        return "UNKNOWN", "manca informazione fisica"

    if V0 < 0.3 and infoP < 0.4:
        return "SAFE", "potenziale basso + informazione bassa"

    elif inertia < 0.15:
        return "ACCESSIBLE", "inerzia informazionale bassa"

    else:
        return "BLACK_HOLE", "inerzia elevata → attrazione informazionale"


print("\n=================================================================")
print(" LOVENTRE INFORMATIONAL ENHANCED PROFILE (v5.3-TER)")
print("=================================================================")
print("json | class | gravity | explanation")
print("-----+-------+---------+--------------------------")

for fname in FILES:
    M = load_metrics(fname)
    kappa, entropy, V0, infoP, inertia, gravity = compute_info(M)
    cl, expl = classify(V0, infoP, inertia)

    grav_str = f"{gravity:.3f}" if gravity is not None else "N/A"
    print(f"{fname:28} | {cl:10} | {grav_str:8} | {expl}")

print("=================================================================\n")

