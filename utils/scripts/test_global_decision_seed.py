from pathlib import Path


def check_seed(path: Path, label: str) -> None:
    if not path.is_file():
        print(f"[FAIL] {label}: file {path.name} NON trovato.")
        return

    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()
    print(f"[OK] {label}: {path.name} esiste ({len(lines)} righe).")

    # Controllino minimale sulle intestazioni principali
    required_headers = ["## 0. Scopo", "## 1.", "## 2."]
    missing = [
        h for h in required_headers
        if not any(h in line for line in lines)
    ]
    if missing:
        print(f"  [WARN] Intestazioni attese non trovate o rinominate: {missing}")
    else:
        print("  [OK] Intestazioni principali presenti.")


def main() -> None:
    root = Path(__file__).resolve().parents[1]

    engine_seed = root / "LOVENTRE_ENGINE_SEED_NOTES.md"
    global_decision_seed = root / "LOVENTRE_GLOBAL_DECISION_SEED_2025-12.md"

    print(f"[INFO] Root project: {root}")
    check_seed(engine_seed, "Engine seed")
    check_seed(global_decision_seed, "Global decision seed")


if __name__ == "__main__":
    main()

