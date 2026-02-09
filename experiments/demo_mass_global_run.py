#!/usr/bin/env python3
"""
LOVENTRE ENGINE – demo_mass_global_run.py

Placeholder / smoke-test per il wrapper:
    meta_decide_instance_with_mass_global(...)

Scopo:
  - verificare che il modulo loventre_meta_decision_engine.py
    sia importabile dalla root dell’engine;
  - verificare che l'attributo meta_decide_instance_with_mass_global
    esista;
  - stampare qualche info di contesto (ENGINE_ROOT, nome funzione,
    docstring sintetica).

Non esegue nessuna istanza reale; questo rimane un demo "di aggancio"
per future integrazioni (Coq, SMS, ecc.).
"""

from __future__ import annotations

import inspect
from pathlib import Path
import sys


def main() -> None:
    # Radice dell'engine (cartella dove risiede questo file)
    engine_root = Path(__file__).resolve().parent
    print("=" * 75)
    print("=== LOVENTRE DEMO – meta_decide_instance_with_mass_global (smoke test) ===")
    print("=" * 75)
    print(f"ENGINE_ROOT: {engine_root}")
    print()

    # Assicuriamo che il root sia nel path di import
    if str(engine_root) not in sys.path:
        sys.path.insert(0, str(engine_root))

    # Import del modulo principale di meta-decisione
    try:
        import loventre_meta_decision_engine as lmd  # type: ignore[import]
    except Exception as e:  # pragma: no cover
        print("[ERRORE] Impossibile importare loventre_meta_decision_engine.")
        print(f"Tipo errore : {type(e).__name__}")
        print(f"Dettaglio   : {e}")
        sys.exit(1)

    # Recupero dell'attributo meta_decide_instance_with_mass_global
    fn = getattr(lmd, "meta_decide_instance_with_mass_global", None)

    if fn is None:
        print(
            "[ERRORE] Nel modulo loventre_meta_decision_engine "
            "non esiste meta_decide_instance_with_mass_global."
        )
        print(
            "Verifica che il wrapper globale sia definito e riesegui "
            "questa demo."
        )
        sys.exit(1)

    print("Wrapper globale trovato:")
    print(f"  modulo : {fn.__module__}")
    print(f"  nome   : {fn.__name__}")
    print()

    # Docstring sintetica (prime righe, se presenti)
    doc = inspect.getdoc(fn) or "(nessuna docstring disponibile)"
    doc_lines = doc.splitlines()
    preview = doc_lines[:8]  # poche righe per non inondare l'output

    print("Docstring (preview):")
    print("-" * 72)
    for line in preview:
        print(line)
    print("-" * 72)
    print()
    print("Nota:")
    print(
        "  Questa demo non esegue realmente il wrapper, ma conferma che "
        "è importabile."
    )
    print(
        "  In futuro qui potremo agganciare Coq, interfacce SMS/CLI o "
        "loader JSON per istanze reali."
    )
    print()
    print("=== FINE DEMO MASS GLOBAL (smoke test) ===")


if __name__ == "__main__":
    main()

