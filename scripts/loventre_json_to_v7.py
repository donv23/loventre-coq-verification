#!/usr/bin/env python3
import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
JSON_DIR = ROOT / "JSON_IO" / "LMetrics_v7_json"
OUT_DIR = ROOT / "Coq_IO" / "LMetrics_v7"

if not JSON_DIR.exists():
    print("[FATAL] Missing JSON directory:", JSON_DIR)
    exit(1)

json_files = sorted(JSON_DIR.glob("m_v7_3sat_DIMACS_*.json"))
if not json_files:
    print("[WARN] No JSON found in", JSON_DIR)
    exit(0)

for jf in json_files:
    name = jf.stem  # ex: m_v7_3sat_DIMACS_01
    out_v = OUT_DIR / f"witness_json_{name}.v"

    with open(jf) as f:
        data = json.load(f)

    # Extract integer metrics (Z)
    vals = [
        int(data.get("kappa_eff", 0)),
        int(data.get("entropy_eff", 0)),
        int(data.get("V0", 0)),
        int(data.get("a_min", 0)),
        int(data.get("p_tunnel", 0)),
        int(data.get("P_success", 0)),
    ]

    coq = []
    coq.append(f"(* Auto-generated from {jf.name} *)")
    coq.append("From Stdlib Require Import ZArith.")
    coq.append("Local Open Scope Z_scope.")
    coq.append("")
    coq.append("From Coq_IO.LMetrics_v7 Require Import LMetrics_v7_types.")
    coq.append("")
    coq.append(f"Definition witness_{name} : LMetricsV7 :=")
    coq.append("  Build_LMetricsV7 " + " ".join(f"{v}%Z" for v in vals) + ".")
    coq.append("")

    with open(out_v, "w") as f:
        f.write("\n".join(coq))

    print(f"[GEN-V7-WITNESS] {out_v.name}")

