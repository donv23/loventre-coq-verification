from pathlib import Path


def main() -> None:
    path = Path("loventre_meta_decision_cli.py")
    if not path.exists():
        print(f"File non trovato: {path}")
        return

    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()

    # Cerchiamo la sezione che stampa "Loventre Policy Bridge"
    target = "Loventre Policy Bridge"
    idx = None
    for i, line in enumerate(lines):
        if target in line:
            idx = i
            break

    if idx is None:
        print("Non trovata alcuna sezione 'Loventre Policy Bridge' in loventre_meta_decision_cli.py")
        return

    start = max(idx - 15, 0)
    end = min(idx + 40, len(lines))

    print("--- SNIPPET loventre_meta_decision_cli.py (Loventre Policy Bridge) ---")
    for j in range(start, end):
        print(f"{j+1:04d}: {lines[j]}")
    print("--- END SNIPPET ---")


if __name__ == "__main__":
    main()

