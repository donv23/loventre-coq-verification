"""
C5.3 — Freeze Integrity Guard
Controlla che i file critici non siano cambiati.
"""

import hashlib
from pathlib import Path

CRITICAL_FILES = [
    "barriers/guard_barrier.py",
    "barriers/monotonicity_barrier.py",
    "barriers/horizon_barrier.py",
    "barriers/safe_compatibility_barrier.py",
    "barriers/robustness_barrier_stack.py",
]

HASH_FILE = Path("audit/C5_FREEZE_HASHES.txt")


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    h.update(path.read_bytes())
    return h.hexdigest()


def compute_hashes() -> dict:
    return {f: sha256(Path(f)) for f in CRITICAL_FILES}


def check_freeze() -> dict:
    if not HASH_FILE.exists():
        HASH_FILE.write_text(
            "\n".join(f"{k} {v}" for k, v in compute_hashes().items())
        )
        return {"freeze_initialized": True}

    stored = {}
    for line in HASH_FILE.read_text().splitlines():
        k, v = line.split()
        stored[k] = v

    current = compute_hashes()
    changed = [k for k in stored if stored[k] != current.get(k)]

    return {
        "freeze_intact": len(changed) == 0,
        "changed_files": changed,
    }


if __name__ == "__main__":
    print(check_freeze())

