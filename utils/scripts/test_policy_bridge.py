from __future__ import annotations

import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from loventre_metrics_bus import new_metrics_bus
from loventre_policy_bridge import decide_from_metrics, GlobalDecision


def show_case(title: str, bus) -> None:
    print(f"\n=== {title} ===")
    decision: GlobalDecision = decide_from_metrics(bus)
    print(f"label  : {decision['label']}")
    print(f"reason : {decision['reason']}")


def main() -> None:
    # Caso 1: rischio basso
    bus_low = new_metrics_bus()
    bus_low["risk_index"] = 0.1
    bus_low["risk_class"] = "low"
    show_case("LOW RISK", bus_low)

    # Caso 2: rischio medio
    bus_med = new_metrics_bus()
    bus_med["risk_index"] = 0.5
    bus_med["risk_class"] = "medium"
    show_case("MEDIUM RISK", bus_med)

    # Caso 3: rischio alto / vicino all'orizzonte
    bus_high = new_metrics_bus()
    bus_high["risk_index"] = 0.9
    bus_high["risk_class"] = "critical"
    bus_high["horizon_flag"] = True
    show_case("HIGH / CRITICAL RISK", bus_high)


if __name__ == "__main__":
    main()

