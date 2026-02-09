# -*- coding: utf-8 -*-
"""
Loventre Meta Engine V6 — supporto completo Global EntryPoint (21 casi)
"""

import json
import os

JSON_DIR = os.path.join(os.path.expanduser("~"),
                        "Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/JSON_IO/LMetrics_v6_cli_bridge")
os.makedirs(JSON_DIR, exist_ok=True)

def run_loventre_meta_engine(kappa=None, entropy=None):
    """
    Meta engine centrale V6
    Calcola decisione Loventre basata su kappa ed entropy
    """
    # Base metrics template
    metrics = {
        'kappa_eff': kappa if kappa is not None else 0.0,
        'entropy_eff': entropy,
        'mass_eff': 1.0,
        'inertial_idx': abs(kappa) if kappa is not None else 0.0,
        'risk_index': abs(kappa) if kappa is not None else 0.0,
        'risk_class': 'LOW',
        'loventre_global_decision': 'SAFE',
        'loventre_global_color': 'GREEN',
        'loventre_global_score': 1.0,
        'meta_label': 'meta_v6_seed'
    }

    # Decision logic
    if kappa is not None:
        if kappa < -0.3:
            metrics['loventre_global_decision'] = 'BLACKHOLE'
            metrics['loventre_global_color'] = 'RED'
            metrics['loventre_global_score'] = 0.0
            metrics['risk_class'] = 'HIGH' if abs(kappa) > 1.0 else 'LOW'
        elif kappa > 1.2:
            metrics['risk_class'] = 'HIGH'
        else:
            metrics['risk_class'] = 'LOW'

    if entropy is not None:
        metrics['entropy_eff'] = entropy
        # Mantieni SAFE se entropy presente, con possibile annotazione
        metrics['loventre_global_decision'] = 'SAFE'
        metrics['loventre_global_color'] = 'GREEN'
        metrics['loventre_global_score'] = 1.0
        metrics['risk_class'] = 'LOW'

    # Generazione JSON case
    filename = f"lmetrics_v6_cli_case_{run_loventre_meta_engine.counter}.json"
    filepath = os.path.join(JSON_DIR, filename)
    with open(filepath, "w") as f:
        json.dump(metrics, f, indent=2)
    
    print(f"[Loventre Meta Engine] run_loventre_meta_engine called with kappa={kappa}, entropy={entropy}")
    print(f"[CASE {run_loventre_meta_engine.counter}] kappa={kappa} entropy={entropy}")
    print(f"  → decision={metrics['loventre_global_decision']} color={metrics['loventre_global_color']} score={metrics['loventre_global_score']} risk={metrics['risk_index']}\n")
    print(f"  ✔ {filename}")

    run_loventre_meta_engine.counter += 1
    return metrics

# Contatore interno per JSON sequenziale
run_loventre_meta_engine.counter = 1

# Helper bridge per compatibilità demo_cli_coq_bridge.py
def meta_decide_instance_with_mass(*args, **kwargs):
    return run_loventre_meta_engine(*args, **kwargs)

def run_loventre_meta_engine_demo():
    """
    Esegue tutte le 21 combinazioni canoniche della Global EntryPoint V6
    """
    # kappa sweep (SAFE → BLACKHOLE)
    kappa_values = [3.0, 2.7, 2.4, 2.1, 1.8, 1.5, 1.2, 0.9, 0.6, 0.3, 0.0,
                    -0.3, -0.6, -0.9, -1.2, -1.5, -1.8, -2.1, -2.4, -2.7, -3.0]
    # entropy sweep
    entropy_values = [None, 1.0, 4.0]  # Demo principali
    
    # Reset counter
    run_loventre_meta_engine.counter = 1

    # Combina kappa + entropy
    for e in entropy_values:
        for k in kappa_values:
            run_loventre_meta_engine(kappa=k, entropy=e)

if __name__ == "__main__":
    run_loventre_meta_engine_demo()

