"""
L14_MULTI_INPUT — V16
=====================

Gestione multi-input:
- riceve lista di raw
- calcola kappa_l1 e entropy per ciascun elemento
- ignora elementi None
- restituisce statistiche aggregate

Output:
{
    "n_effective": n,
    "kappa_list": [...],
    "entropy_list": [...],
    "kappa_mean": <float or None>,
    "entropy_mean": <float or None>,
    "kappa_spread": <float or None>,
}
"""

from V13_NEXT.L10_SUPERENTRYPOINT.loventre_superentrypoint_l10_v13 import run_l10_superentrypoint_v13
from V14_NEXT.l14_snapshot_builder import build_v14_snapshot

def compute_multi_input_stats(raw_list):
    if raw_list is None:
        return {}

    kappas = []
    entropies = []

    for raw in raw_list:
        v13 = run_l10_superentrypoint_v13(raw)
        v14 = build_v14_snapshot(v13)

        k = v14.get("kappa_l1")
        e = v14.get("entropy_eff")

        if k is not None:
            kappas.append(k)
        if e is not None:
            entropies.append(e)

    n = len(kappas)
    if n == 0:
        return {
            "n_effective": 0,
            "kappa_list": [],
            "entropy_list": [],
            "kappa_mean": None,
            "entropy_mean": None,
            "kappa_spread": None,
        }

    kmin = min(kappas)
    kmax = max(kappas)
    spread = kmax - kmin
    kmean = sum(kappas) / n
    emean = sum(entropies) / n if entropies else None

    return {
        "n_effective": n,
        "kappa_list": kappas,
        "entropy_list": entropies,
        "kappa_mean": round(kmean, 6),
        "entropy_mean": round(emean, 6),
        "kappa_spread": round(spread, 6),
    }

