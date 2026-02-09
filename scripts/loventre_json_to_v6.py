#!/usr/bin/env python3

import os, json

ROOT = os.path.dirname(os.path.abspath(__file__)) + "/.."
JSON_DIR = ROOT + "/3SAT_MINIBRIDGE/json_out"
OUT_DIR  = ROOT + "/Coq_IO/LMetrics_v6"

def fmt(x):
    return f"{x:.2f}"   # Due decimali max

def emit(data):
    meta = data.get("meta_label", 0)
    fname = f"witness_json_m_v6_seed_{meta:02d}.v"
    out_path = f"{OUT_DIR}/{fname}"
    with open(out_path, "w") as f:
        f.write("From Stdlib Require Import Reals String.\n")
        f.write("From LMetrics_v6 Require Import LMetrics_v6_types.\n\n")
        f.write(f"Definition witness_json_m_v6_seed_{meta:02d} : LMetrics := mkLMetrics (\n")
        f.write(f"  {fmt(data['kappa_eff'])} ) (\n")
        f.write(f"  {fmt(data['entropy_eff'])} ) (\n")
        f.write(f"  {fmt(data['mass_eff'])} ) (\n")
        f.write(f"  {fmt(data['inertial_idx'])} ) (\n")
        f.write(f"  {fmt(data['risk_index'])} ) (\n")
        f.write(f"  {data['risk_class']} ) (\n")
        f.write(f"  {data['loventre_global_decision']} ) (\n")
        f.write(f"  {data['loventre_global_color']} ) (\n")
        f.write(f"  {fmt(data['loventre_global_score'])} ) (\n")
        f.write(f"  {meta} ) (\n")
        f.write(f"  \"{data['source_file']}\" ).\n")
    print(f"[GEN] {fname}")

if __name__ == "__main__":
    for jf in os.listdir(JSON_DIR):
        if jf.endswith(".json"):
            with open(f"{JSON_DIR}/{jf}") as fp:
                data = json.load(fp)
                emit(data)

