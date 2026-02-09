"""
L14_EXPORT_FOR_COQ — V19
========================

Genera JSON LMetrics compatibili con Coq.

Campi estratti:
- state
- kappa_l1
- entropy_eff
- policy_dynamic (se presente, altrimenti policy)
- version
- timestamp
"""

import json
import os
from V14_NEXT.l14_snapshot_builder import build_v14_snapshot
from V14_NEXT.l14_timestamp_hash import attach_identity_fields
from V14_NEXT.l14_policy_dynamic import compute_policy_dynamic
from V14_NEXT.l14_history_core import record_event

# Dove scrivere il JSON
EXPORT_DIR = "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/JSON_IO/LMetrics_v3_for_Coq"


def extract_lmetrics(snapshot_v14):
    """
    Seleziona solo i campi accettati da Coq LMetrics v1.
    """
    if not isinstance(snapshot_v14, dict):
        return {}

    state = snapshot_v14.get("state")
    k = snapshot_v14.get("kappa_l1")
    e = snapshot_v14.get("entropy_eff")
    pol = snapshot_v14.get("policy_dynamic", snapshot_v14.get("policy"))
    ver = snapshot_v14.get("version")
    ts = snapshot_v14.get("timestamp")

    return {
        "state": state,
        "kappa_l1": k,
        "entropy_eff": e,
        "policy": pol,
        "version": ver,
        "timestamp": ts,
    }


def run_export_for_coq_v19(raw_value=0.6):
    """
    Passi:
    1. Esegue superentry V13
    2. Normalizza V14
    3. Timestamp + hash
    4. Policy dinamica
    5. Estrae campi Coq
    6. Scrive JSON nel folder Coq
    7. Registra storia
    """
    from V13_NEXT.L10_SUPERENTRYPOINT.loventre_superentrypoint_l10_v13 import (
        run_l10_superentrypoint_v13,
    )

    v13 = run_l10_superentrypoint_v13(raw_value)
    base = build_v14_snapshot(v13)
    snap = attach_identity_fields(base)
    snap["policy_dynamic"] = compute_policy_dynamic(snap)

    lmetrics = extract_lmetrics(snap)

    if not os.path.exists(EXPORT_DIR):
        os.makedirs(EXPORT_DIR, exist_ok=True)

    fname = f"lmetrics_coq_u{str(raw_value).replace('.', '_')}.json"
    with open(os.path.join(EXPORT_DIR, fname), "w") as f:
        json.dump(lmetrics, f, indent=2)

    record_event(snap)
    return True

