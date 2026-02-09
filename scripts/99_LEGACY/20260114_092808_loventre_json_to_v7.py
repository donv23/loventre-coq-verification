#!/usr/bin/env python3
# ============================================================
# LOVENTRE ENGINE v7 — JSON → Witness Coq (Z-only generator)
# ============================================================

import json
import os
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
JSON_DIR = ROOT / "3SAT_MINIBRIDGE" / "json_out"
OUT_DIR = ROOT / "Coq_IO" / "LMetrics_v7"

SCALE = 100  # deterministic scaling float->Z

def scale_z(x):
    try:
        return int(round(float(x) * SCALE))
    except:
        return 0

def main():
    files = sorted(JSON_DIR.glob("*.json"))
    for idx, f in enumerate(files, 1):
        with f.open() as fh:
            data = json.load(fh)

        k = scale_z(data.get("kappa_eff", 0))
        e = scale_z(data.get("entropy_eff", 0))
        m = scale_z(data.get("mass_eff", 0))
        i = scale_z(data.get("inertial_idx", 0))
        r = scale_z(data.get("risk_index", 0))

        meta = int(data.get("meta_label", idx))

        outname = OUT_DIR / f"witness_json_{f.stem}.v"

        coq = f"""(* Auto-generated from {f.name} *)
Require Import LMetrics_v7_import.

Definition witness_{f.stem} : LMetricsV7 :=
  Build_LMetricsV7 {k}%Z {e}%Z {m}%Z {i}%Z {r}%Z {meta}.

"""

        with outname.open("w") as out:
            out.write(coq)

        print(f"[GEN-V7-WITNESS] {outname.name}")

if __name__ == "__main__":
    main()

