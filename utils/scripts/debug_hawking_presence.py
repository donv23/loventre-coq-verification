import json
import sys
from pathlib import Path

# Aggancia la root del progetto al sys.path
THIS_FILE = Path(__file__).resolve()
ROOT = THIS_FILE.parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from loventre_meta_decision_engine import meta_decide_instance_with_mass


def main() -> None:
    history_path = ROOT / "esempio_history.json"
    if not history_path.exists():
        print(f"⚠️  File non trovato: {history_path}")
        return

    data = json.loads(history_path.read_text(encoding="utf-8"))

    # Usiamo la stessa chiamata del debug_policy_bridge_example
    result = meta_decide_instance_with_mass(data, E=1.5)

    print("=== HAWKING FIELDS IN METRICS ===")
    found = False
    for k in sorted(result.keys()):
        if "hawking" in k.lower():
            print(f"{k}: {result[k]!r}")
            found = True

    if not found:
        print("(nessuna chiave contenente 'hawking' trovata in metrics)")

    print("\n=== META_EXPLANATION CONTAINS 'Hawking'? ===")
    meta_expl = result.get("meta_explanation", "")
    if "Hawking" in meta_expl or "Hawking–Loventre" in meta_expl:
        print("Sì: meta_explanation contiene una sezione Hawking–Loventre.")
    else:
        print("No: meta_explanation NON contiene la stringa 'Hawking'.")
        print("Lunghezza meta_explanation:", len(meta_expl))


if __name__ == "__main__":
    main()

