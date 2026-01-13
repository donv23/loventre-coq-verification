"""
demo_mass_global_run.py

Mini-demo per verificare che il wrapper
meta_decide_instance_with_mass_global sia importabile
dal progetto Loventre Engine, anche se lanciamo lo script
dalla cartella Loventre_Coq_Clean.
"""

import sys
from pathlib import Path

# 1. Aggiungiamo il path del Loventre Engine all'import di Python
ENGINE_ROOT = Path(
    "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/"
    "ALGORITIMIA/LOVENTRE_ENGINE_CLEAN/loventre_engine_clean_seed"
)

if str(ENGINE_ROOT) not in sys.path:
    sys.path.append(str(ENGINE_ROOT))

# 2. Ora possiamo importare il wrapper globale
from loventre_meta_decision_engine import meta_decide_instance_with_mass_global  # noqa: E402


def main() -> None:
    print("[Loventre] Demo meta_decide_instance_with_mass_global (placeholder).")
    print("  ENGINE_ROOT =", ENGINE_ROOT)
    print("  Funzione disponibile:", meta_decide_instance_with_mass_global.__name__)

    # Quando avremo una vera 'instance' del motore, qui potremo fare:
    # instance = ...
    # res = meta_decide_instance_with_mass_global(
    #     instance,
    #     n_budget=1000,
    #     family="seed_grid",
    # )
    # print(res["metrics"]["loventre_global"]["global_decision"])
    # print(res["metrics"]["loventre_global"]["global_color"])
    # print(res["metrics"]["loventre_global"]["global_score"])


if __name__ == "__main__":
    main()

