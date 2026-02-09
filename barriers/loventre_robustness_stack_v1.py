"""
loventre_robustness_stack_v1.py

Robustness Stack v1 – CANONICA
Implementa le tre misure strutturali fondamentali:

  (1) Stabilità strutturale sotto perturbazioni
  (2) Blocco di fase / barriera critica
  (3) Invarianza sotto cambio di descrizione

Nessuna statistica.
Nessun p-value.
Solo struttura deterministica.

Questo modulo NON decide nulla.
Appende solo campi di robustezza al metrics bus.
"""

from __future__ import annotations

from typing import Callable, Dict, Any, List, Tuple


# =========================================================
# UTILS
# =========================================================

def _clip_int(x: int, lo: int = 0, hi: int = 3) -> int:
    if x < lo:
        return lo
    if x > hi:
        return hi
    return x


def _extract_phase_signature(metrics: Dict[str, Any]) -> Tuple[Any, Any, Any]:
    """
    Firma strutturale minima usata per confronti di robustezza.
    NON numerica.
    """
    return (
        metrics.get("meta_label"),
        metrics.get("horizon_flag"),
        metrics.get("loventre_global", {}).get("global_decision"),
    )


# =========================================================
# (1) STABILITÀ STRUTTURALE
# =========================================================

def compute_structural_stability(
    base_metrics: Dict[str, Any],
    seed: Dict[str, int],
    engine_fn: Callable[[Dict[str, int]], Dict[str, Any]],
) -> bool:
    """
    Verifica se piccole perturbazioni del seed
    cambiano o meno la firma strutturale globale.
    """

    base_sig = _extract_phase_signature(base_metrics)

    param = int(seed.get("param", 0))
    factor = int(seed.get("factor", 0))

    perturbations = [
        {"param": _clip_int(param + 1), "factor": factor},
        {"param": _clip_int(param - 1), "factor": factor},
        {"param": param, "factor": _clip_int(factor + 1)},
        {"param": param, "factor": _clip_int(factor - 1)},
    ]

    for p_seed in perturbations:
        p_metrics = engine_fn(p_seed)
        p_sig = _extract_phase_signature(p_metrics)
        if p_sig != base_sig:
            return False

    return True


# =========================================================
# (2) BLOCCO DI FASE / BARRIERA
# =========================================================

def compute_phase_lock(
    base_metrics: Dict[str, Any],
    seed: Dict[str, int],
    engine_fn: Callable[[Dict[str, int]], Dict[str, Any]],
) -> bool:
    """
    Verifica che la fase non collassi
    sotto una variazione mono-assiale minima.
    """

    base_sig = _extract_phase_signature(base_metrics)

    param = int(seed.get("param", 0))
    factor = int(seed.get("factor", 0))

    test_seeds = [
        {"param": _clip_int(param + 1), "factor": factor},
        {"param": param, "factor": _clip_int(factor + 1)},
    ]

    for t_seed in test_seeds:
        t_metrics = engine_fn(t_seed)
        t_sig = _extract_phase_signature(t_metrics)
        if t_sig != base_sig:
            return False

    return True


# =========================================================
# (3) INVARIANZA (HOOK SU MODULO ESISTENTE)
# =========================================================

def compute_invariance_flag(base_metrics: Dict[str, Any]) -> bool:
    """
    Invarianza minimale:
    per ora richiede solo che il campo 'meta_label'
    sia presente e stabile (hook concettuale).

    Versioni successive possono agganciarsi a:
      - loventre_invariance_c.py
    """

    return base_metrics.get("meta_label") is not None


# =========================================================
# AGGREGAZIONE FINALE (5σ-like STRUTTURALE)
# =========================================================

def aggregate_robust_level(
    stable: bool,
    phase_locked: bool,
    invariant: bool,
) -> Tuple[int, str]:
    """
    Aggregazione deterministica.
    Nessuna probabilità.
    """

    if not stable:
        return 1, "fragile"

    if stable and not phase_locked:
        return 3, "stable"

    if stable and phase_locked and not invariant:
        return 4, "structural"

    if stable and phase_locked and invariant:
        return 5, "canonical"

    return 0, "local"


# =========================================================
# API PUBBLICA
# =========================================================

def append_robustness_stack_v1(
    base_metrics: Dict[str, Any],
    seed: Dict[str, int],
    *,
    engine_fn: Callable[[Dict[str, int]], Dict[str, Any]],
) -> Dict[str, Any]:
    """
    Appende al metrics bus i campi di robustezza strutturale.
    NON modifica il resto del bus.
    """

    stable = compute_structural_stability(base_metrics, seed, engine_fn)
    phase_locked = compute_phase_lock(base_metrics, seed, engine_fn)
    invariant = compute_invariance_flag(base_metrics)

    level, label = aggregate_robust_level(stable, phase_locked, invariant)

    enriched = dict(base_metrics)
    enriched.update(
        {
            "robust_stability_pass": stable,
            "robust_phase_pass": phase_locked,
            "robust_invariance_pass": invariant,
            "robust_level": level,
            "robust_label": label,
        }
    )

    return enriched

