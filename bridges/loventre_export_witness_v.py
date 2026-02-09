"""
loventre_export_witness_v.py
Generatore di witness Coq da JSON canonico
FASE 4.8
"""

import json
import os
from typing import Dict, Any


def generate_witness_v(json_path: str, outdir: str = "canon_coq") -> str:
    with open(json_path, "r", encoding="utf-8") as f:
        data = json.load(f)

    seed = data["seed"]
    M = data["LMetrics"]

    name = f"m_seed_{seed['param']}_{seed['factor']}"
    filename = f"{name}.v"

    content = f"""
From Loventre_Advanced.Geometry Require Import Loventre_LMetrics_Structure.

Definition {name} : LMetrics :=
{{
  kappa_eff := {M['kappa_eff']};
  entropy_eff := {M['entropy_eff']};
  V0 := {M['V0']};
  p_tunnel := {M['p_tunnel']};
  P_success := {M['P_success']};
  barrier_tag := 0;
  informational_potential := 0
}}.
"""

    os.makedirs(outdir, exist_ok=True)
    path = os.path.join(outdir, filename)

    with open(path, "w", encoding="utf-8") as f:
        f.write(content.strip() + "\n")

    return path

