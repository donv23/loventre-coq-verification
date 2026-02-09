"""
demo_global_entrypoint.py
---------------------------------
Entry point globale del Loventre Engine.
Verifica che il motore si avvii, importi i moduli core e mostri le docstring.
"""

import sys
import importlib

print("===================================================================")
print("=== LOVENTRE GLOBAL ENTRYPOINT (bootstrap test)                 ===")
print("===================================================================\n")

modules = [
    "loventre_instance_analysis",
    "loventre_metrics_bus",
    "loventre_meta_decision_engine",
]

for name in modules:
    try:
        mod = importlib.import_module(name)
        print(f"[OK  ] modulo importato: {name}")
        doc = (mod.__doc__ or "").strip().splitlines()[0] if mod.__doc__ else "(no doc)"
        print(f"       docstring: {doc}")
    except Exception as e:
        print(f"[FAIL] errore importando {name}: {e}")

print("\nPython executable:", sys.executable)
print("\n[ OK ] demo_global_entrypoint.py")

