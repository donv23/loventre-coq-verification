#!/usr/bin/env python3
import pathlib

def main():
    root = pathlib.Path(__file__).resolve().parents[1]

    # directory candidate per il "core"
    candidate_dirs = [
        root / "loventre" / "core",
        root / "loventre" / "engine",
        root / "core",
        root / "engine",
    ]

    py_files = []

    for d in candidate_dirs:
        if d.exists() and d.is_dir():
            for f in d.glob("*.py"):
                py_files.append(f)

    if not py_files:
        print("[Loventre] Nessun file core/engine trovato nelle directory candidate.")
        return

    total = 0
    for path in sorted(py_files):
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            print(f"[Loventre] WARNING: impossibile leggere {path}")
            continue
        n = len(text.splitlines())
        total += n
        rel = path.relative_to(root)
        print(f"{n:6d} {rel}")

    print(f"{total:6d} totale core/engine")

if __name__ == "__main__":
    main()

