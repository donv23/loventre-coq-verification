"""
loventre_export_canon_json.py
Export JSON canonico Loventre → Coq
FASE 4.7
"""

import json
from typing import Dict, Any


def export_canon_json(record: Dict[str, Any], outdir: str = "canon_json") -> str:
    """
    Esporta una decisione Loventre in JSON canonico compatibile Coq
    """
    seed = record["seed"]
    metrics = record["metrics"]

    payload = {
        "seed": seed,
        "LMetrics": {
            "kappa_eff": metrics["kappa_eff"],
            "entropy_eff": metrics["entropy_eff"],
            "V0": metrics["V0"],
            "p_tunnel": metrics["p_tunnel"],
            "P_success": metrics["P_success"],
        },
        "decision": record["decision"],
        "mode": record["mode"],
    }

    filename = f"canon_seed_{seed['param']}_{seed['factor']}.json"

    import os
    os.makedirs(outdir, exist_ok=True)
    path = os.path.join(outdir, filename)

    with open(path, "w", encoding="utf-8") as f:
        json.dump(payload, f, indent=2)

    return path

