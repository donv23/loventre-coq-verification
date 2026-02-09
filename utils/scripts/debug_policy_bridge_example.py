import json
import sys
from pathlib import Path

# Aggancia la root del progetto al sys.path, anche se eseguiamo da scripts/
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

    # Usiamo la stessa firma della CLI: history, E
    result = meta_decide_instance_with_mass(data, E=1.5)

    print("=== DEBUG POLICY BRIDGE – KEYS ===")
    for k in sorted(result.keys()):
        if (
            k.startswith("policy_")
            or k.startswith("policy")
            or k == "policy_bridge_warning"
        ):
            print(f"{k}: {result[k]!r}")

    print("\n=== DEBUG POLICY BRIDGE – META EXPLANATION (ULTIME RIGHE) ===")
    meta_expl = result.get("meta_explanation", "")
    if not meta_expl:
        print("(meta_explanation vuota o assente)")
        return

    lines = meta_expl.splitlines()
    tail = lines[-12:] if len(lines) > 12 else lines
    for line in tail:
        print(line)


if __name__ == "__main__":
    main()

