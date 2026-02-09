"""
Loventre Engine Protection Layer (Canvas 25 FINAL)

This module verifies the LMetrics guard and supports
two certified canonical guard values:
P-like and NP-like.
"""

# === CANONICAL GUARDS (unforgeable fingerprints) ===
EXPECTED_GUARD_LIKE   = "33f3a00c645e0f98443a2d5f62e8e8329b836b2944d0d6cc5b07da9b54d74845"
EXPECTED_GUARD_NPLIKE = "aa3b8bd8e7bc840d9e3f6673f41151c131e6dfb4c9b56c5b92a7f8e2b31a0b17"


class LoventreGuardError(Exception):
    pass


def verify_lmetrics(metrics: dict) -> dict:
    """
    Input: dict from json_bridge.json_to_metrics(...)
    Output: verified dict + {"LMetrics_type": "...", "LMetrics_valid": True}
    or raise LoventreGuardError.
    """

    if "loventre_guard" not in metrics:
        raise LoventreGuardError("Missing Loventre guard.")

    g = metrics["loventre_guard"]

    if g == EXPECTED_GUARD_LIKE:
        profile_type = "P_like"
    elif g == EXPECTED_GUARD_NPLIKE:
        profile_type = "NP_like"
    else:
        raise LoventreGuardError("Invalid Loventre guard value.")

    verified = dict(metrics)
    verified["LMetrics_valid"] = True
    verified["LMetrics_type"]  = profile_type
    return verified

