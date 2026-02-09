"""
Test V14 — Timestamp + Hash
===========================

Verifica che:
- timestamp venga aggiunto
- hash venga aggiunta
- hash cambi se cambia input
"""

from V14_NEXT.l14_timestamp_hash import add_timestamp_and_hash

def test_timestamp_and_hash():
    base = {"state": "SAFE", "kappa_l1": 0.7}
    a = add_timestamp_and_hash(base)
    b = add_timestamp_and_hash(base)
    assert "timestamp" in a
    assert "hash" in a
    assert a != b, "Hash o timestamp devono essere diversi tra chiamate"

