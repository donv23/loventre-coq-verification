"""
L3_DECISION — V12
Converte etichette bus "-ish" in decisioni leggibili
"""

from typing import Dict, Any
from L0_CORE.loventre_utils_core_v12 import clamp01
from L0_CORE.loventre_labels_core_v12 import (
    SAFE_ISH,
    P_ACC_ISH,
    BLACKHOLE_ISH,
    UNDEFINED_ISH,
    SAFE,
    SAFE_ACCESSIBLE,
    BLACKHOLE,
    WAIT
)

def decide_l3(bus_result: Dict[str, Any]) -> Dict[str, Any]:
    """
    Input expected:
        {
            'kappa_l1': float|None,
            'bus_label': SAFE_ISH | P_ACC_ISH | BLACKHOLE_ISH | UNDEFINED_ISH
        }
    Output:
        {
            'decision_l3': str,
            'confidence_l3': float,
            'note': str
        }
    """
    bus_label = bus_result.get("bus_label")
    kappa_l1 = bus_result.get("kappa_l1")

    # fallback
    if bus_label == UNDEFINED_ISH:
        return {
            "decision_l3": WAIT,
            "confidence_l3": 0.0,
            "note": "undefined inputs"
        }

    # BLACKHOLE-ish → BLACKHOLE
    if bus_label == BLACKHOLE_ISH:
        return {
            "decision_l3": BLACKHOLE,
            "confidence_l3": 0.0,
            "note": "absorbed"
        }

    # SAFE-ish → SAFE (medium confidence)
    if bus_label == SAFE_ISH:
        return {
            "decision_l3": SAFE,
            "confidence_l3": clamp01((kappa_l1 or 0.0) * 0.7),
            "note": "ordinary safe"
        }

    # P_ACC-ish → SAFE_ACCESSIBLE (max confidence)
    if bus_label == P_ACC_ISH:
        return {
            "decision_l3": SAFE_ACCESSIBLE,
            "confidence_l3": clamp01((kappa_l1 or 1.0)),
            "note": "peak accessible"
        }

    # unreachable fallback
    return {
        "decision_l3": WAIT,
        "confidence_l3": 0.0,
        "note": "unexpected bus_label"
    }


# DEMO
def demo():
    cases = [
        {"kappa_l1": None, "bus_label": UNDEFINED_ISH},
        {"kappa_l1": -0.1, "bus_label": BLACKHOLE_ISH},
        {"kappa_l1": 0.2, "bus_label": SAFE_ISH},
        {"kappa_l1": 0.8, "bus_label": P_ACC_ISH},
        {"kappa_l1": 1.0, "bus_label": P_ACC_ISH},
    ]
    print("\n=== DEMO L3 DECISION V12 ===")
    for case in cases:
        out = decide_l3(case)
        print(f"in={case} → dec={out['decision_l3']:>16} | conf={out['confidence_l3']:.2f} | {out['note']}")


if __name__ == "__main__":
    demo()

