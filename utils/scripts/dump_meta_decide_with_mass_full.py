from pathlib import Path


def main() -> None:
    path = Path("loventre_meta_decision_engine.py")
    if not path.exists():
        print(f"File non trovato: {path}")
        return

    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()

    target = "def meta_decide_instance_with_mass"
    start = None
    for i, line in enumerate(lines):
        if target in line:
            start = i
            break

    if start is None:
        print(f"Non trovata la funzione {target}")
        return

    # Troviamo la prossima def a colonna 0 (inizio nuova funzione)
    end = len(lines)
    for j in range(start + 1, len(lines)):
        if lines[j].startswith("def "):
            end = j
            break

    print("--- FULL meta_decide_instance_with_mass ---")
    for k in range(start, end):
        print(f"{k+1:04d}: {lines[k]}")
    print("--- END FULL meta_decide_instance_with_mass ---")


if __name__ == "__main__":
    main()

