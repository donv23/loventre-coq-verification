"""
L14_BLACKHOLE_MONITOR — V20
===========================

Osserva sequenze di esecuzioni
e verifica se mai avviene transizione:

    BLACKHOLE → SAFE o SAFE_ACCESSIBLE

Produzione:
- se succede almeno una volta → salva "counterexample"
- se NON succede → claim osservativo positivo
"""

import random
import json
import os
from V14_NEXT.l14_snapshot_builder import build_v14_snapshot
from V14_NEXT.l14_timestamp_hash import attach_identity_fields
from V14_NEXT.l14_policy_dynamic import compute_policy_dynamic
from V14_NEXT.l14_history_core import record_event

EXPORT_DIR = "/Users/vincenzoloventre/Library/Mobile Documents/com~apple~CloudDocs/ALGORITIMIA/JSON_IO/LMetrics_v3_for_Coq"


def run_sequence_v20(num_steps=50):
    """
    Esegue N run casuali del motore.
    Controlla transizioni dallo stato precedente.
    """
    from V13_NEXT.L10_SUPERENTRYPOINT.loventre_superentrypoint_l10_v13 import (
        run_l10_superentrypoint_v13,
    )

    last_state = None
    counterexample = None
    trace = []

    for _ in range(num_steps):
        raw = random.uniform(0.0, 1.0)
        
        v13 = run_l10_superentrypoint_v13(raw)
        base = build_v14_snapshot(v13)
        snap = attach_identity_fields(base)

        # policy dinamica integrata
        snap["policy_dynamic"] = compute_policy_dynamic(snap)

        state = snap.get("state")
        trace.append(state)

        # check transizione BH → SAFE/PACC
        if last_state == "BLACKHOLE" and state in ("SAFE", "SAFE_ACCESSIBLE"):
            counterexample = {
                "last_state": last_state,
                "next_state": state,
                "raw": raw,
                "snapshot": snap,
            }
            break

        last_state = state

        record_event(snap)

    return {
        "counterexample": counterexample,
        "trace": trace,
        "num_steps": num_steps,
    }

