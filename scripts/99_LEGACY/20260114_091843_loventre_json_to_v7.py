#!/usr/bin/env python3
import json, os

SRC_DIR = "3SAT_MINIBRIDGE/json_out"
DST_DIR = "Coq_IO/LMetrics_v7"

def emit_v7(fn):
    with open(fn,"r") as f:
        data=json.load(f)

    base = os.path.splitext(os.path.basename(fn))[0]
    outvn = f"witness_json_{base}.v"
    outpath = os.path.join(DST_DIR,outvn)

    v = f"""Require Import Coq_IO.LMetrics_v7.LMetrics_v7_import.

Definition m_{base} : LMetrics_v7 :=
  {{|
    kappa_eff := {data["kappa_eff"]};
    entropy_eff := {data["entropy_eff"]};
    mass_eff := {data["mass_eff"]};
    inertial_idx := {data["inertial_idx"]};
    risk_index := {data["risk_index"]};
    risk_class := "{data["risk_class"]}";
    loventre_global_decision := "{data["loventre_global_decision"]}";
    loventre_global_color := "{data["loventre_global_color"]}";
    loventre_global_score := {data["loventre_global_score"]};
    meta_label := {data["meta_label"]};
    source_file := "{data["source_file"]}"
  |}}.
"""

    with open(outpath,"w") as g:
        g.write(v)

if __name__=="__main__":
    for fn in os.listdir(SRC_DIR):
        if not fn.endswith(".json"): continue
        emit_v7(os.path.join(SRC_DIR,fn))

