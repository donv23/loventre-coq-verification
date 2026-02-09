"""
L14_SNAPSHOT_BUILDER — V15 (con entropy_eff)
============================================

Estende builder V14 aggiungendo entropy_eff.
"""

from V14_NEXT.l14_export_canon import get_export_template
from V14_NEXT.l14_entropy import compute_entropy_eff

def build_v14_snapshot(v13_snapshot):
    """
    Mappa uno snapshot di V13 in struttura V14 con entropy_eff.
    """
    snap = get_export_template()

    if not isinstance(v13_snapshot, dict):
        return snap

    # Copia campi V13 rilevanti
    for key in ["state", "kappa_l1", "policy", "router_target", "consistency_flag"]:
        if key in v13_snapshot:
            snap[key] = v13_snapshot[key]

    # Entropia
    snap["entropy_eff"] = compute_entropy_eff(snap.get("kappa_l1"))

    return snap

