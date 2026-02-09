from __future__ import annotations

import importlib
import platform
import sys
from pathlib import Path


MODULES_TO_CHECK = [
    "loventre_meta_portfolio_lab",
    "loventre_adaptive_field",
    "loventre_schwarzschild_lab",
    "loventre_meta_decision_engine",
    "loventre_meta_decision_cli",
]


def main() -> None:
    print("=== Loventre Engine diagnostics ===")
    print(f"Python version : {sys.version.split()[0]}")
    print(f"Platform       : {platform.platform()}")
    print(f"Working dir    : {Path(__file__).resolve().parent}")
    print()

    for name in MODULES_TO_CHECK:
        print(f"- Checking module: {name}")
        try:
            mod = importlib.import_module(name)
        except Exception as e:  # noqa: BLE001
            print(f"  [FAIL] cannot import {name} -> {e.__class__.__name__}: {e}")
        else:
            version = getattr(mod, "__version__", None)
            if version is None:
                print(f"  [OK]   {name} imported (no __version__ attribute)")
            else:
                print(f"  [OK]   {name} imported (version={version!r})")

    print()
    print("=== End diagnostics ===")


if __name__ == "__main__":
    main()
