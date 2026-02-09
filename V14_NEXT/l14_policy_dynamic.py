"""
L14_POLICY_DYNAMIC — V18
========================

Definisce una policy dinamica basata sulla storia recente.
Usa compute_history_summary() da V17.
"""

from V14_NEXT.l14_history_core import compute_history_summary


def compute_policy_dynamic(snapshot_v14):
    """
    Restituisce una policy dinamica basata sulla memoria minima.
    """
    summary = compute_history_summary()
    total = summary.get("total", 0)

    # fallback: se non abbiamo storia, restituiamo policy originale
    if total == 0:
        return snapshot_v14.get("policy", "DO_NOTHING")

    bh = summary.get("blackhole", 0)
    safe = summary.get("safe", 0)
    pacc = summary.get("safe_accessible", 0)

    # Domina BH → prudenza
    if bh > safe + pacc:
        return "DO_NOTHING"

    # Domina SAFE_ACCESSIBLE → consolidiamo ma senza rischio
    if pacc >= safe and pacc > bh:
        return "STEADY"

    # SAFE prevalente → possiamo tentare di esplorare
    if safe > pacc + bh:
        return "EXPLORE_MORE"

    # fallback neutro
    return snapshot_v14.get("policy", "STEADY")

