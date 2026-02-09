#!/usr/bin/env python3

import json
from pprint import pprint

from loventre_global_from_json import run_global_from_json
from loventre_gct_diagnosis import gct_diagnosis
from loventre_policy_bridge import apply_policy_bridge
from loventre_meta_decision_engine import global_meta_decision


def run_full_test(name, json_path):
    print("\n" + "=" * 80)
    print(f"FULL ENGINE DIAGNOSTIC TEST — {name}")
    print("=" * 80)

    # 1️⃣ Load JSON
    with open(json_path, "r") as f:
        seed = json.load(f)

    print("\n[INPUT SEED]")
    pprint(seed)

    # 2️⃣ Core pipeline → metrics bus
    metrics = run_global_from_json(seed)

    print("\n[METRICS BUS — RAW]")
    for k in sorted(metrics.keys()):
        print(f"{k:35s}: {metrics[k]}")

    # 3️⃣ GCT analysis
    gct = gct_diagnosis(metrics)

    print("\n[GCT DIAGNOSIS]")
    for k in sorted(gct.keys()):
        print(f"{k:35s}: {gct[k]}")

    # 4️⃣ Policy bridge
    metrics_with_policy = apply_policy_bridge(metrics)

    print("\n[METRICS AFTER POLICY BRIDGE]")
    for k in sorted(metrics_with_policy.keys()):
        print(f"{k:35s}: {metrics_with_policy[k]}")

    # 5️⃣ Global decision
    decision = global_meta_decision(metrics_with_policy)

    print("\n[GLOBAL META DECISION]")
    pprint(decision)

    print("\n" + "=" * 80)
    print("END OF TEST")
    print("=" * 80)

    return decision


def main():
    print("\nLOVENTRE ENGINE — FULL DIAGNOSTIC RUN\n")

    run_full_test(
        "P-like SAFE witness",
        "metrics_seed11_cli_demo.json"
    )

    run_full_test(
        "NP-like critical witness",
        "metrics_SAT_crit16_demo_with_global.json"
    )

    print("\nALL TESTS COMPLETED\n")


if __name__ == "__main__":
    main()

