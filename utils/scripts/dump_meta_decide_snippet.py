from pathlib import Path


def main() -> None:
    path = Path("loventre_meta_decision_engine.py")
    if not path.exists():
        print(f"File non trovato: {path}")
        return

    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()

    target = "def meta_decide_instance_with_mass"
    idx = None
    for i, line in enumerate(lines):
        if target in line:
            idx = i
            break

    if idx is None:
        print(f"Non trovata la funzione {target}")
        return

    start = max(idx - 5, 0)
    end = min(idx + 80, len(lines))

    print("--- SNIPPET meta_decide_instance_with_mass ---")
    for j in range(start, end):
        print(f"{j+1:04d}: {lines[j]}")
    print("--- END SNIPPET ---")


if __name__ == "__main__":
    main()

