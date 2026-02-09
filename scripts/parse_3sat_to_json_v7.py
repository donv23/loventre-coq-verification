#!/usr/bin/env python3
import os, json, math
from pathlib import Path

# ==========================================================
# LOVENTRE ENGINE v7
# parse_3sat_to_json_v7.py
# Estrae (vars, clauses), calcola metriche base
# e introduce RISK QUADRATICO
# ==========================================================

ROOT = Path(__file__).resolve().parent.parent
IN_DIR = ROOT / "3SAT_MINIBRIDGE" / "input_dimacs"
OUT_DIR = ROOT / "3SAT_MINIBRIDGE" / "json_out"

OUT_DIR.mkdir(parents=True, exist_ok=True)


def parse_dimacs(path):
    vars_seen = set()
    clauses = 0
    with open(path) as f:
        for line in f:
            line = line.strip()
            if not line or line.startswith('c'):
                continue
            if line.startswith('p'):
                continue
            clauses += 1
            parts = line.split()
            for lit in parts:
                try:
                    v = abs(int(lit))
                    if v > 0:
                        vars_seen.add(v)
                except:
                    pass
    return len(vars_seen), clauses


def compute_metrics(nvars, nclauses):
    # Normalizzazioni v7
    kappa = min(1.0, (nclauses / max(1,nvars)) * 0.1 + 0.2)
    entropy = min(1.0, 0.3 + (nclauses / max(1,nvars)) * 0.1)
    mass = (kappa + entropy) / 2

    # RISK QUADRATICO (NOVITÀ v7)
    ratio = nclauses / max(1, nvars)
    risk = min(1.0, ratio * ratio)   # (C/V)^2

    # Classificazione semplice
    if risk < 0.2:
        risk_class = "LOW"
        decision = "SAFE"
        color = "GREEN"
        score = 0.8
    elif risk < 0.35:
        risk_class = "MEDIUM"
        decision = "SAFE"
        color = "YELLOW"
        score = 0.45
    else:
        risk_class = "HIGH"
        decision = "UNSAFE"
        color = "RED"
        score = 0.15

    return {
        "kappa_eff": kappa,
        "entropy_eff": entropy,
        "mass_eff": mass,
        "inertial_idx": (kappa + mass) / 2,
        "risk_index": risk,
        "risk_class": risk_class,
        "loventre_global_decision": decision,
        "loventre_global_color": color,
        "loventre_global_score": score,
    }


def main():
    files = sorted(IN_DIR.glob("*.cnf"))
    print("==============================================")
    print(" LOVENTRE ENGINE v7 — parse DIMACS → JSON")
    print("==============================================")
    for idx, cnf in enumerate(files, start=1):
        nvars, nclauses = parse_dimacs(cnf)
        metrics = compute_metrics(nvars, nclauses)
        metrics["meta_label"] = idx
        metrics["source_file"] = cnf.name
        out = OUT_DIR / f"m_v7_3sat_DIMACS_{idx:02d}.json"
        with open(out, "w") as f:
            json.dump(metrics, f, indent=2)
        print(f"[GEN-v7] {out.name} (vars={nvars}, clauses={nclauses})")


if __name__ == "__main__":
    main()

