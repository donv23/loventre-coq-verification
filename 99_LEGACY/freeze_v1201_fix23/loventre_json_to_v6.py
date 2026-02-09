#!/usr/bin/env python3
"""
LOVENTRE ENGINE — v1201 JSON→Coq Bridge
Legge JSON da JSON_IO_v6/
e genera Coq_IO/LMetrics_v6/witness_json_<name>.v
"""

import os, json, sys

ROOT = os.path.expanduser("~/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed")
JSON_DIR = os.path.join(ROOT, "JSON_IO_v6")
TARGET_DIR = os.path.join(ROOT, "Coq_IO/LMetrics_v6")

def render(record, fname):
    return f"""
(** Auto-generated from JSON: {fname} *)
From Stdlib Require Import Reals.
From Stdlib Require Import String.
From LMetrics_v6 Require Import LMetrics_v6_types.

Definition {fname}_example : LMetrics :=
  mkLMetrics
    {record['kappa_eff']}%R
    {record['entropy_eff']}%R
    {record['mass_eff']}%R
    {record['inertial_idx']}%R
    {record['risk_index']}%R
    {record['risk_class']}
    {record['loventre_global_decision']}
    {record['loventre_global_color']}
    {record['loventre_global_score']}%R
    {record['meta_label']}
    "{record['source_file']}"%string.
"""

def main():
    for file in os.listdir(JSON_DIR):
        if not file.endswith(".json"):
            continue
        path = os.path.join(JSON_DIR, file)
        with open(path) as f:
            rec = json.load(f)

        fname = file.replace(".json", "")
        coq_name = f"witness_json_{fname}.v"
        out = render(rec, fname)

        target = os.path.join(TARGET_DIR, coq_name)
        with open(target, "w") as out_file:
            out_file.write(out)

        print(f"[GEN] {coq_name}")

if __name__ == "__main__":
    main()

