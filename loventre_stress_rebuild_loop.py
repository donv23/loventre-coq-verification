import json
import random
import subprocess
from pathlib import Path
import shutil
import time


JSONS = [
    "metrics_2SAT_easy_demo.json",
    "metrics_2SAT_crit_demo.json",
]

EPS = 0.05
ROUNDS = 30


def perturb_json(src, dst):
    data = json.loads(Path(src).read_text())
    for k, v in data.items():
        if isinstance(v, (int, float)):
            data[k] = max(0.0, v * (1.0 + random.uniform(-EPS, EPS)))
    Path(dst).write_text(json.dumps(data, indent=2))


def run():
    print("[Loventre] Stress rebuild loop avviato\n")

    for src in JSONS:
        if not Path(src).exists():
            print(f"[SKIP] {src} non trovato")
            continue

        print(f"\n=== SOURCE {src} ===")

        for i in range(ROUNDS):
            tmp = f"_tmp_{i}_{src}"
            perturb_json(src, tmp)

            try:
                subprocess.check_call(
                    ["python3", "loventre_build_lmetrics_from_json.py", tmp],
                    stdout=subprocess.DEVNULL,
                    stderr=subprocess.DEVNULL,
                )
                print(f"[ OK ] round {i:02d}")
            except Exception:
                print(f"[FAIL] round {i:02d}")
                raise
            finally:
                Path(tmp).unlink(missing_ok=True)

    print("\n[Loventre] Stress rebuild completato senza errori.")


if __name__ == "__main__":
    run()

