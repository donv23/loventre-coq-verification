"""
robustness_barrier_stack.py

Stack di barriere strutturali Loventre.
Ogni barriera è teorema-like: non stima, non decide, non corregge.
"""

from typing import Dict, Any, Optional

from barriers.guard_barrier import apply_guard_barrier
from barriers.horizon_barrier import apply_horizon_barrier
from barriers.monotonicity_barrier import apply_monotonicity_barrier
from barriers.safe_compatibility_barrier import apply_safe_compatibility_barrier


def apply_robustness_barrier_stack(
    metrics: Dict[str, Any],
    metrics_prev: Optional[Dict[str, Any]] = None,
) -> Dict[str, Any]:
    """
    Applica in sequenza tutte le barriere strutturali.
    Ordine canonico:
      1. Guard
      2. Orizzonte (BH)
      3. Monotonicità
      4. SAFE compatibility
    """

    verified = apply_guard_barrier(metrics)

    if metrics_prev is not None:
        verified = apply_horizon_barrier(metrics_prev, verified)
        verified = apply_monotonicity_barrier(metrics_prev, verified)

    verified = apply_safe_compatibility_barrier(verified)

    return verified

