"""
L14_TIMESTAMP_HASH — V14.2
==========================

Aggiunge:
- version_id
- timestamp ISO8601
- sha256 hash del contenuto snapshot base

Funzione pubblica:
attach_identity_fields(snapshot: dict) -> dict
"""

import hashlib
from datetime import datetime
import json

VERSION_ID = "V14.2"


def compute_hash(snapshot):
    """
    Calcola sha256 sul JSON canonico senza version/timestamp/hash.
    """
    if not isinstance(snapshot, dict):
        return None

    filtered = {k: v for k, v in snapshot.items() if k not in ("version", "timestamp", "hash")}
    try:
        payload = json.dumps(filtered, sort_keys=True).encode("utf-8")
        return hashlib.sha256(payload).hexdigest()
    except Exception:
        return None


def attach_identity_fields(snapshot):
    """
    Aggiunge campi canonici:
    - version
    - timestamp ISO
    - hash SHA256
    """
    if not isinstance(snapshot, dict):
        return snapshot

    iso = datetime.utcnow().isoformat() + "Z"
    h = compute_hash(snapshot)

    snap = dict(snapshot)
    snap["version"] = VERSION_ID
    snap["timestamp"] = iso
    snap["hash"] = h
    return snap

