import json
import copy
import random
from pathlib import Path

from loventre_meta_decision_engine import apply_policy_bridge_to_metrics


JSON_FILES = [
    "metrics_2SAT_easy_demo.json",
    "metrics_2SAT_crit_demo.json",
]

EPS = 0.05  # perturbazione controllata


def perturb(metrics, key):
    if key not in metrics:
        return metrics
    if not isinstance(metrics[key], (int, float)):
        return metrics
    m = copy.deepcopy(metrics)
    m[key] = max(0.0, m[key] * (1.0 + random.uniform(-EPS, EPS)))
    return m


def run():
    print("[Loventre] Avvio stress test di perturbazione JSON\n")

    for jf in JSON_FILES:
        path = Path(jf)
        if not path.exists():
            print(f"[SKIP] {jf} non trovato")
            continue

        base = json.loads(path.read_text())
        keys = list(base.keys())

        print(f"\n=== FILE: {jf} ===")

        for k in keys:
            test_metrics = perturb(base, k)
            try:
                apply_policy_bridge_to_metrics(test_metrics)
                decision = test_metrics.get("loventre_global_decision")
                color = test_metrics.get("loventre_global_color")
                meta = test_metrics.get("meta_label")
                print(
                    f"[ OK ] perturb {k:20s} → "
                    f"decision={decision}, color={color}, meta={meta}"
                )
            except Exception as e:
                print(f"[FAIL] perturb {k}: {e}")
                raise

    print("\n[Loventre] Stress test completato senza errori.")


if __name__ == "__main__":
    run()

