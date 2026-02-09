"""
V13_NEXT / loventre_metrics_l1_v13.py
------------------------------------
Layer 1 V13: estrazione e normalizzazione metrica di kappa grezzo.

Versione indipendente:
  • rinominato compute_l1_metrics_v13
  • riferimenti a L0_CORE immutati
  • nessun use di altri livelli
"""

from L0_CORE.loventre_utils_core_v12 import safe_numeric, clamp01
from L0_CORE.loventre_labels_core_v12 import SAFE, BLACKHOLE, WAIT


def compute_l1_metrics_v13(raw_value=None):
    """
    Normalizza un valore grezzo di kappa:
      - None  -> None + WAIT
      - [-1,+1] clampato + SAFE
      - fuori range -> clamp + BLACKHOLE (assorbito)
    """

    if raw_value is None:
        return {
            "kappa_l1": None,
            "status": WAIT,
        }

    x = safe_numeric(raw_value)
    x_clamped = clamp01(x)

    if x < 0:
        status = BLACKHOLE
    else:
        status = SAFE

    return {
        "kappa_l1": x_clamped,
        "status": status,
    }


def demo():
    print("=== DEMO L1 METRICS V13 ===")
    samples = [None, -1.0, -0.3, 0.0, 0.2, 0.8, 3.0]

    for raw in samples:
        out = compute_l1_metrics_v13(raw)
        kappa_str = (
            f"{out['kappa_l1']:.2f}"
            if isinstance(out["kappa_l1"], (int, float))
            else str(out["kappa_l1"])
        )
        print(
            f"raw={str(raw):>4} → kappa_l1={kappa_str:>6} | status={out['status']}"
        )


if __name__ == "__main__":
    demo()

