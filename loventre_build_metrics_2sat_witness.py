#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
loventre_build_metrics_2sat_witness.py

Costruisce i due witness JSON della famiglia 2-SAT:
    - metrics_2SAT_easy_demo.json
    - metrics_2SAT_crit_demo.json

usando il motore geometrico Loventre (loventre_sat_2sat_family)
e il contratto del bus centrale (loventre_metrics_bus).
"""

import json
import pathlib
from typing import Any, Dict

from loventre_metrics_bus import new_metrics_bus, validate_metrics_bus
from loventre_sat_2sat_family import summarize_2sat_instance


ROOT = pathlib.Path(__file__).resolve().parent


def build_metrics_from_summary(summary: Dict[str, Any]) -> Dict[str, Any]:
    """
    Converte il dizionario di summary (geometria 2-SAT) in un metrics completo.

    Riempie il Loventre Metrics Bus con i valori calcolati
    e aggiunge i campi Loventre standard (meta_label, risk_class, ecc.).
    """
    bus = new_metrics_bus()

    # Campi geometrici fondamentali
    bus["kappa_eff"] = summary["kappa_eff"]
    bus["entropy_eff"] = summary["entropy_eff"]
    bus["V0"] = summary["V0"]
    bus["a_min"] = 4.0  # costante A_MIN_SAT
    bus["p_tunnel"] = summary["p_tunnel"]
    bus["P_success"] = summary["P_success"]

    # Campi di default coerenti
    bus["gamma_dilation"] = 1.0
    bus["time_regime"] = "time_euclidean"
    bus["mass_eff"] = 1.0
    bus["inertial_idx"] = 1.0
    bus["risk_index"] = 0.0
    bus["risk_class"] = summary.get("target_risk_class", "risk_LOW")
    bus["chi_compactness"] = 0.0
    bus["horizon_flag"] = False

    # Etichette e policy hint
    metrics: Dict[str, Any] = dict(bus)
    metrics["meta_label"] = summary.get("target_meta_label", "meta_UNKNOWN")
    metrics["loventre_global_decision"] = summary.get("target_global_decision", "GD_safe")
    metrics["loventre_global_color"] = summary.get("target_global_color", "GC_green")

    # Wrap finale (annidiamo anche info di provenienza)
    metrics["loventre_family"] = {
        "family": "2SAT_demo_family",
        "regime_hint": summary.get("regime_hint"),
        "description": summary.get("description"),
    }

    validate_metrics_bus(bus)
    return metrics


def main() -> None:
    print("===================================================================")
    print("=== LOVENTRE BUILDER – 2-SAT FAMILY WITNESS                    ===")
    print("===================================================================\n")

    targets = [
        ("2SAT_easy_demo", "metrics_2SAT_easy_demo.json"),
        ("2SAT_crit_demo", "metrics_2SAT_crit_demo.json"),
    ]

    for name, out_name in targets:
        print(f"[BUILD] Generazione {out_name} ← {name}")
        summary = summarize_2sat_instance(name, energy=0.5, n_budget=10000)
        metrics = build_metrics_from_summary(summary)

        out_path = ROOT / out_name
        with out_path.open("w", encoding="utf-8") as f:
            json.dump(metrics, f, indent=2, sort_keys=True, ensure_ascii=False)
        print(f"[OK] Salvato: {out_path.name}")
        print(f"    meta_label={metrics['meta_label']}")
        print(f"    risk_class={metrics['risk_class']}")
        print(f"    decision={metrics['loventre_global_decision']}")
        print(f"    color={metrics['loventre_global_color']}")
        print()

    print(">>> FINE BUILDER 2-SAT – JSON aggiornati e compatibili con il Metrics Bus.\n")


if __name__ == "__main__":
    main()

