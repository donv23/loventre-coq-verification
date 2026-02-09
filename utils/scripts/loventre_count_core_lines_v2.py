#!/usr/bin/env python3
import pathlib

EXCLUDE_SUFFIXES = ("_test.py", "_legacy.py", "_deprecated.py", "_sandbox.py")
EXCLUDE_PREFIXES = ("test_",)


def is_core_file(path: pathlib.Path, root: pathlib.Path) -> bool:
    # esclude scripts/ e __pycache__ dal conteggio
    rel = path.relative_to(root)
    parts = rel.parts
    if parts[0] in {"scripts", "__pycache__"}:
        return False

    name = path.name
    if any(name.endswith(suf) for suf in EXCLUDE_SUFFIXES):
        return False
    if any(name.startswith(pre) for pre in EXCLUDE_PREFIXES):
        return False

    return True


def main():
    root = pathlib.Path(__file__).resolve().parents[1]

    py_files = set()

    # 1) file core nello stile "seed": loventre_*.py nella root del progetto
    for f in root.glob("loventre_*.py"):
        if f.is_file():
            py_files.add(f)

    # 2) vecchio stile, se mai presente: loventre/core, loventre/engine, core, engine
    candidate_dirs = [
        root / "loventre" / "core",
        root / "loventre" / "engine",
        root / "core",
        root / "engine",
    ]

    for d in candidate_dirs:
        if d.exists() and d.is_dir():
            for f in d.glob("*.py"):
                if f.is_file():
                    py_files.add(f)

    core_files = [f for f in py_files if is_core_file(f, root)]

    if not core_files:
        print("[Loventre] Nessun file core trovato (loventre_*.py o core/engine).")
        return

    total = 0
    for path in sorted(core_files):
        text = path.read_text(encoding="utf-8")
        n = len(text.splitlines())
        rel = path.relative_to(root)
        print(f"{n:6d} {rel}")
        total += n

    print(f"{total:6d} totale core")


if __name__ == "__main__":
    main()

