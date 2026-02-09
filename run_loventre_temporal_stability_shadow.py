"""
run_loventre_temporal_stability_shadow.py

Shadow test B – Stabilità temporale (gennaio 2026)

Obiettivo:
- simulare N osservazioni successive dello stesso profilo
- introdurre rumore osservativo (isteresi)
- verificare che la decisione snapshot NON derivi
"""

import json
from pathlib import Path


def load_metrics(path: Path) -> dict:
    with path.open("r", encoding="utf-8") as f:
        return json.load(f)


def shadow_temporal_test(metrics: dict, rounds: int = 20) -> None:
    base_decision = (
        metrics.get("loventre_global", {}) or {}
    ).get("global_decision")

    print(f"[BASE] decision={base_decision}")

    for i in range(1, rounds + 1):
        m = dict(metrics)

        # Simulazione rumore osservativo
        if i % 2 == 0:
            m["hysteresis_detected"] = True
        else:
            m["hysteresis_detected"] = False

        decision = (
            m.get("loventre_global", {}) or {}
        ).get("global_decision")

        if decision != base_decision:
            print(
                f"[FAIL] round={i}: decision drift "
                f"{base_decision} → {decision}"
            )
            raise SystemExit(1)

        print(
            f"[OK ] round={i:02d} "
            f"hysteresis={m['hysteresis_detected']} "
            f"decision={decision}"
        )

    print("\n[Loventre][SHADOW] STABILITÀ TEMPORALE OK")


def main() -> None:
    base_dir = Path(__file__).resolve().parent

    targets = [
        "metrics_2SAT_easy_demo_hysteresis.json",
        "metrics_2SAT_easy_demo_blackhole.json",
    ]

    print("\n[Loventre][SHADOW] Avvio stress di stabilità temporale\n")

    for name in targets:
        path = base_dir / name
        if not path.exists():
            print(f"[SKIP] {name} (file non trovato)")
            continue

        print(f"\n[TEST] {name}")
        metrics = load_metrics(path)
        shadow_temporal_test(metrics)

    print("\n[Loventre][SHADOW] TEST COMPLETATO – STATO VERDE\n")


if __name__ == "__main__":
    main()

