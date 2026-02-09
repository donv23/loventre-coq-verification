"""
V22 — Transition Counter
Conta transizioni tra stati informazionali usando V21 memory.
"""

from V21_NEXT.l21_memory_core import tail_memory

def compute_transition_counts(window=100):
    """
    Restituisce un dict:
    {
        "SAFE->SAFE": 3,
        "SAFE->ACCESSIBLE": 1,
        ...
    }
    """
    recent = tail_memory(window)
    counts = {}

    last = None
    for r in recent:
        curr = r.get("decision")
        if curr is None:
            continue
        if last is not None:
            key = f"{last}->{curr}"
            counts[key] = counts.get(key, 0) + 1
        last = curr

    return counts

