"""
L14_EXPORT_ACT_DYNAMIC — V18
============================

Versione export che applica policy dinamica.
"""

import json
import os
from V14_NEXT.l14_snapshot_builder import build_v14_snapshot
from V14_NEXT.l14_timestamp_hash import attach_identity_fields
from V14_NEXT.l14_history_core import record_event
from V14_NEXT.l14_policy_dynamic import compute_policy_dynamic

OUTPUT_DIR = "V14_JSON_CANON"


def run_export_l14_dynamic(raw_value=0.4):
    from V13_NEXT.L10_SUPERENTRYPOINT.loventre_superentrypoint_l10_v13 import (
        run_l10_superentrypoint_v13,
    )

    v13 = run_l10_superentrypoint_v13(raw_value)
    snap = build_v14_snapshot(v13)
    snap = attach_identity_fields(snap)

    # Sovrascrive policy usando la memoria
    snap["policy_dynamic"] = compute_policy_dynamic(snap)

    fname = f"v14_dynamic_u{str(raw_value).replace('.', '_')}.json"

    if not os.path.exists(OUTPUT_DIR):
        os.makedirs(OUTPUT_DIR, exist_ok=True)

    with open(os.path.join(OUTPUT_DIR, fname), "w") as f:
        json.dump(snap, f, indent=2)

    # Storicizza
    record_event(snap)

    return True

