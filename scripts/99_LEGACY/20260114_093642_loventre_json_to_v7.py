#!/usr/bin/env python3
import json
import pathlib

# =========================================================
# LOVENTRE — JSON → LMetrics v7 Coq generator
# v2026-01-14 — modern Stdlib imports + clean formatting
# =========================================================

ROOT = pathlib.Path(__file__).resolve().parent.parent
JSON_DIR = ROOT / "JSON_IO" / "LMetrics_v7_json"
COQ_OUT = ROOT / "Coq_IO" / "LMetrics_v7"

def generate_one(json_path: pathlib.Path, index: int):
    with open(json_path, "r") as f:
        data = json.load(f)

    # Coq numeric fields MUST end in %Z
    fields = [
        data.get("kappa_eff", 0),
        data.get("entropy_eff", 0),
        data.get("V0", 0),
        data.get("a_min", 0),
        data.get("p_tunnel", 0),
        data.get("P_success", 0),
    ]

    fname = f"witness_json_m_v7_3sat_DIMACS_{index:02d}.v"
    out_path = COQ_OUT / fname

    with open(out_path, "w") as out:
        out.write(f"(* Auto-generated from {json_path.name} *)\n")
        out.write("From Stdlib Require Import ZArith.\n")
        out.write("From LMetrics_v7 Require Import LMetrics_v7_types.\n")
        out.write("Local Open Scope Z_scope.\n\n")
        out.write(f"Definition witness_m_v7_3sat_DIMACS_{index:02d} : LMetricsV7 :=\n")
        out.write("  Build_LMetricsV7 ")
        out.write(" ".join(f"{v}%Z" for v in fields))
        out.write(".\n")

    print(f"[GEN-V7-WITNESS] {fname}")

def main():
    COQ_OUT.mkdir(parents=True, exist_ok=True)

    paths = sorted(JSON_DIR.glob("m_v7_3sat_DIMACS_*.json"))
    if not paths:
        print("[WARN] No JSON found in JSON_IO/LMetrics_v7_json")
        return

    for idx, path in enumerate(paths, start=1):
        generate_one(path, idx)

if __name__ == "__main__":
    main()

