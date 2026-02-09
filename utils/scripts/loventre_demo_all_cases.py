#!/usr/bin/env python3
"""
loventre_demo_all_cases.py

Regia compatta dei tre demo Loventre:

- DEMO CASE 1 – buco nero supercritico, UV neutro
- DEMO CASE 2 – buco nero di frontiera UV
- DEMO CASE 3 – scenario manovrabile / precritico

Per ciascun caso:
  - richiama il rispettivo demo (riusando le sue funzioni)
  - stampa solo un riepilogo sintetico leggibile
"""

import importlib
import sys


def _load_case_module(name: str):
    try:
        return importlib.import_module(name)
    except Exception as e:
        print(f"[ERROR] Impossibile importare modulo {name!r}: {e}")
        sys.exit(1)


def _print_summary(label: str, metrics: dict) -> None:
    def g(key, default=None):
        return metrics.get(key, default)

    print("=" * 72)
    print(f"[{label}]")
    print(f"  risk_index           : {g('risk_index')!r}")
    print(f"  schwarzschild_regime : {g('schwarzschild_regime')!r}")
    print(f"  hawking_regime       : {g('hawking_regime')!r}")
    print(f"  hawking_uv_phase     : {g('hawking_uv_phase')!r}")
    print(f"  policy_uv_tag        : {g('policy_uv_tag')!r}")
    print(f"  policy_strategy      : {g('policy_strategy')!r}")
    print(f"  policy_energy        : {g('policy_energy')!r}")
    comment = g("policy_comment")
    if comment:
        print("  policy_comment:")
        print("   ", comment)
    print()


def main() -> None:
    # Import dei tre demo case (sono tutti in scripts/, quindi import diretti)
    case1 = _load_case_module("loventre_demo_case_1")
    case2 = _load_case_module("loventre_demo_case_2")
    case3 = _load_case_module("loventre_demo_case_3")

    # CASE 1 – buco nero supercritico, UV neutro
    lmd1 = case1.import_meta_engine()
    core1 = case1.build_synthetic_core_metrics()
    metrics1 = case1.run_pipeline(lmd1, dict(core1))
    _print_summary("DEMO CASE 1 – buco nero supercritico", metrics1)

    # CASE 2 – buco nero di frontiera UV (usa la pipeline con forcing UV)
    lmd2 = case2.import_meta_engine()
    core2 = case2.build_frontier_core_metrics()
    metrics2 = case2.run_pipeline_frontier(lmd2, dict(core2))
    _print_summary("DEMO CASE 2 – frontiera Hawking UV", metrics2)

    # CASE 3 – scenario manovrabile / precritico
    lmd3 = case3.import_meta_engine()
    core3 = case3.build_manageable_core_metrics()
    metrics3 = case3.run_pipeline_manageable(lmd3, dict(core3))
    _print_summary("DEMO CASE 3 – precritico manovrabile", metrics3)


if __name__ == "__main__":
    main()

