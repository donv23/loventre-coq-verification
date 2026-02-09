"""
LOVENTRE ENGINE v7 — Exporter LMetrics -> Coq ingestible .v
Stadio 2.4 — Subfix 2.4.2
"""

import json
import pathlib
from typing import Dict, Any

# Importiamo la policy v7 (fix del nome!)
from loventre_policy_bridge_v7 import classify_json_dict


# ================================
# Directory di input e output
# ================================
JSON_DIR = pathlib.Path("./JSON_IO/LMetrics_v7")        # sorgenti JSON v7
COQ_OUT_DIR = pathlib.Path("./Coq_IO/LMetrics_v7_export")  # destinazione .v


# ================================
# Carica JSON singolo
# ================================
def load_json_metrics(path: pathlib.Path) -> Dict[str, Any]:
    with open(path, "r", encoding="utf-8") as fh:
        return json.load(fh)


# ================================
# Applica policy
# ================================
def apply_policy(m: Dict[str, Any]) -> Dict[str, Any]:
    try:
        c = classify_json_dict(m)
        out = dict(m)
        out["class_v7"] = c.get("class_v7", "unknown")
        out["score_v7"] = int(c.get("score_v7", 0))
        out["safe_flag"] = bool(c.get("safe_flag", True))
        return out
    except Exception:
        return dict(m)


# ================================
# Converte dizionario finale in snippet Coq
# ================================
def emit_coq_snippet(name: str, d: Dict[str, Any]) -> str:
    ctor = (
        f"Build_LMetricsV7"
        f" {d.get('kappa_eff',0)}%Z"
        f" {d.get('entropy_eff',0)}%Z"
        f" {d.get('mass_eff',0)}%Z"
        f" {d.get('inertial_idx',0)}%Z"
        f" {d.get('risk_index',0)}%Z"
        f" {d.get('meta_label',0)}%Z"
    )
    return f"Definition {name} : LMetricsV7 := {ctor}.\n"


# ====================================
# Scrive file Coq .v per una singola istanza JSON
# ====================================
def export_one_json(path: pathlib.Path) -> pathlib.Path:
    raw = load_json_metrics(path)
    met = apply_policy(raw)
    base = path.stem
    coq_name = base.replace("-", "_")
    snippet = emit_coq_snippet(coq_name, met)

    COQ_OUT_DIR.mkdir(parents=True, exist_ok=True)
    out = COQ_OUT_DIR / f"{coq_name}.v"
    with open(out, "w", encoding="utf-8") as fh:
        fh.write(
f"""(* Auto-generated from JSON {path.name} *)
From Stdlib Require Import ZArith.
Local Open Scope Z_scope.

From LMetrics_v7 Require Import LMetrics_v7_types.

{snippet}
"""
        )
    return out


# ====================================
# Processo completo per tutta la cartella sorgente
# ====================================
def export_all():
    JSON_DIR.mkdir(parents=True, exist_ok=True)
    files = list(JSON_DIR.glob("*.json"))
    results = []
    for p in files:
        try:
            out = export_one_json(p)
            print(f"[OK] {p.name} -> {out}")
            results.append(out)
        except Exception as e:
            print(f"[FAIL] {p.name}: {e}")
    return results


if __name__ == "__main__":
    export_all()
    print("[DONE] LMetrics v7 export complete")

