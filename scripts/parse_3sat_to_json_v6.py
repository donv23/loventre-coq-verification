#!/usr/bin/env python3

"""
LOVENTRE ENGINE — parse_3sat_to_json_v6.py
Converte un file DIMACS 3-SAT in JSON v6 compatibile
Output: 3SAT_MINIBRIDGE/json_out/m_v6_3sat_DIMACS_##.json
"""

import os, json, sys, random

ROOT = os.path.dirname(os.path.abspath(__file__)) + "/.."
IN_DIR = ROOT + "/3SAT_MINIBRIDGE/input_dimacs"
OUT_DIR = ROOT + "/3SAT_MINIBRIDGE/json_out"

def parse_dimacs(path):
    vars_count = 0
    clauses_count = 0

    with open(path) as fp:
        for line in fp:
            line=line.strip()
            if not line or line.startswith('c'): 
                continue
            if line.startswith('p cnf'):
                parts = line.split()
                vars_count = int(parts[2])
                clauses_count = int(parts[3])
            elif line.endswith('0'):
                clauses_count += 0  # già contato nel header

    return vars_count, clauses_count

def compute_metrics(nvars, nclauses):
    # METRICHE GREZZE (placeholder)
    ratio = nclauses / max(1, nvars)
    kappa = min(1.0, 0.2 + ratio * 0.1)
    entropy = min(1.0, 0.3 + ratio * 0.2)
    mass = min(1.0, 0.25 + ratio * 0.15)
    inertia = min(1.0, 0.22 + ratio * 0.1)
    risk = min(1.0, ratio * 0.25)

    # decisione iniziale molto grezza
    if risk < 0.33:
        rc = "LOW"; dec="SAFE"; col="GREEN"; score=0.75
    elif risk < 0.66:
        rc = "MEDIUM"; dec="SAFE"; col="YELLOW"; score=0.45
    else:
        rc = "HIGH"; dec="UNSAFE"; col="RED"; score=0.15

    return dict(
        kappa_eff=kappa,
        entropy_eff=entropy,
        mass_eff=mass,
        inertial_idx=inertia,
        risk_index=risk,
        risk_class=rc,
        loventre_global_decision=dec,
        loventre_global_color=col,
        loventre_global_score=score
    )

def run():
    os.makedirs(OUT_DIR, exist_ok=True)
    files = [f for f in os.listdir(IN_DIR) if f.endswith(".cnf")]
    if not files:
        print("[ERR] Nessun file CNF trovato in", IN_DIR)
        sys.exit(1)

    for idx,f in enumerate(files, start=1):
        path = f"{IN_DIR}/{f}"
        nvars, nclauses = parse_dimacs(path)
        metrics = compute_metrics(nvars, nclauses)

        meta = idx
        jname = f"m_v6_3sat_DIMACS_{meta:02d}.json"
        out = {
            **metrics,
            "meta_label": meta,
            "source_file": jname
        }

        with open(f"{OUT_DIR}/{jname}", "w") as fp:
            json.dump(out, fp, indent=2)

        print(f"[GEN-JSON] {jname}  (vars={nvars}, clauses={nclauses})")

if __name__ == "__main__":
    run()

