from pathlib import Path


MODULE_CONTENT = '''"""Central metrics bus for the Loventre Engine.

This module defines the canonical set of keys that every metrics dict
should use. The goal is that all labs (instance analysis, SAT/TSP
families, global profile, meta-portfolio, ...) can pass around a single
standard structure without guessing key names.

The philosophy is:
- keep metrics as a flat dict (no nested structures), so that printing
  and tabular views stay simple;
- still provide a single place where the canonical key names live;
- allow older code to keep its own extra keys: we never delete them,
  we only make sure the Loventre keys are present.

Typical usage
-------------
- For a new metrics dict:

    from loventre_metrics_bus import new_metrics

    m = new_metrics(
        family_label="TSP_crit_n",
        instance_label="tsp_crit_16",
        problem_type="TSP",
    )
    m["kappa_eff"] = kappa_eff
    m["entropy_eff"] = entropy_eff
    ...

- To normalise an existing dict:

    from loventre_metrics_bus import ensure_loventre_keys

    metrics = ensure_loventre_keys(raw_metrics)

The list of keys below is intentionally a bit larger than what any
single module needs; think of it as the "Loventre vocabulary" that
every lab can rely on.
"""

from __future__ import annotations

from typing import Dict, Mapping, MutableMapping, Set


# --- Canonical key groups -------------------------------------------------


#: Core geometric / barrier / tunneling keys for a single instance or
#: an effective point representing a family.
CORE_KEYS = [
    # Geometric / informational geometry
    "kappa_eff",           # effective curvature (scalar summary)
    "entropy_eff",         # effective entropy (scalar summary)

    # Barrier geometry
    "V0",                  # barrier height (potential threshold)
    "a_min",               # minimal barrier thickness (in steps)
    "barrier_occupancy",   # fraction of steps with U >= V0

    # Energetic / tunneling layer
    "E",                   # effective energy used in p_tunnel
    "p_tunnel",            # tunneling probability at energy E
    "expected_attempts",   # E[N] ≈ 1 / p_tunnel (if defined)
    "P_success",           # success probability with given budget
]


#: Time-dilation / difficulty keys (internal Loventre time).
TIME_KEYS = [
    "redshift_inf",        # -ln(p_tunnel) when 0 < p < 1
    "gamma_dilation",      # 1 + redshift_inf
    "difficulty_index",    # gamma_dilation * barrier_occupancy
    "difficulty_label",    # qualitative label (easy / hard / ...)
    "time_regime",         # time_euclidean / threshold / hyperbolic
]


#: Horizon / black-hole detection keys.
HORIZON_KEYS = [
    "horizon_detected",    # bool: complexity horizon present
    "black_hole_risk",     # bool: strong black-hole regime
    "window_barrier_occ",  # barrier occupancy in final window
    "window_U_min",        # min U in final window
    "window_U_max",        # max U in final window
    "window_U_mean",       # mean U in final window
]


#: Metadata and classification keys, shared across seeds / SAT / TSP
#: and critical families.
META_KEYS = [
    "family_label",        # e.g. "TSP_standard", "TSP_crit_n", "SAT_crit_n", "SEED"
    "instance_label",      # e.g. "tsp10", "sat_crit12", "(param=2,factor=3)"
    "problem_type",        # e.g. "TSP", "SAT", "SEED", "GENERIC"

    # Spatial / NP-like classification in the Loventre sense
    "region_label",        # "regular" / "precritical" / "critical"
    "np_like_label",       # "P_like" / "NP_like_critical" / None
    "pattern_c",           # e.g. "regular", "geometric_precritical", ...

    # Portfolio / decision layer
    "decision_label",      # e.g. "Altamente raccomandato", "Quasi impossibile"
    "score",               # generic numeric score (meta-portfolio)
]


#: Extra structural metadata specific to some families (not always used).
STRUCTURAL_KEYS = [
    "n_cities",            # for TSP instances
    "n_vars",              # for SAT instances
    "n_clauses",           # for SAT instances

    # For seed grid (param, factor) if one wants to store them explicitly
    "seed_param",
    "seed_factor",
]


#: Optional trace keys for richer analysis (not needed in dashboards but
#: useful for debugging and labs).
TRACE_KEYS = [
    "U_values",            # list/array of U(t) along the history
    "kappa_values",        # list/array of kappa(t)
]


ALL_KEYS: Set[str] = set().union(
    CORE_KEYS,
    TIME_KEYS,
    HORIZON_KEYS,
    META_KEYS,
    STRUCTURAL_KEYS,
    TRACE_KEYS,
)


# --- Human-readable documentation for each key ----------------------------


METRIC_DOC: Dict[str, str] = {
    # Core geometric / tunneling
    "kappa_eff": "Effective curvature summarising the instance/family.",
    "entropy_eff": "Effective entropy summarising the instance/family.",
    "V0": "Barrier height (Loventre potential threshold).",
    "a_min": "Minimal barrier thickness where U >= V0.",
    "barrier_occupancy": "Fraction of steps with U >= V0 along the history.",
    "E": "Effective energy used in tunneling computations.",
    "p_tunnel": "Tunneling probability at energy E.",
    "expected_attempts": "Expected number of attempts E[N] ≈ 1 / p_tunnel.",
    "P_success": "Success probability with the chosen attempt budget.",

    # Time / difficulty
    "redshift_inf": "-ln(p_tunnel) when 0 < p_tunnel < 1.",
    "gamma_dilation": "Internal time dilation factor: 1 + redshift_inf.",
    "difficulty_index": "gamma_dilation * barrier_occupancy.",
    "difficulty_label": "Qualitative difficulty label (e.g. easy / hard).",
    "time_regime": "Time regime: euclidean / threshold / hyperbolic.",

    # Horizon / black-hole layer
    "horizon_detected": "True if a complexity horizon is detected.",
    "black_hole_risk": "True if instance is in black-hole regime.",
    "window_barrier_occ": "Barrier occupancy in the final time window.",
    "window_U_min": "Minimum U in the final window.",
    "window_U_max": "Maximum U in the final window.",
    "window_U_mean": "Mean U in the final window.",

    # Metadata / classification / portfolio
    "family_label": "Family name (TSP_standard, TSP_crit_n, SAT_crit_n, SEED, ...).",
    "instance_label": "Instance identifier inside the family.",
    "problem_type": "High-level type: TSP / SAT / SEED / GENERIC.",
    "region_label": "Spatial classification: regular / precritical / critical.",
    "np_like_label": "Loventre complexity label: P_like / NP_like_critical.",
    "pattern_c": "Pattern of curvature/complexity (regular / mixed / fully_critical / ...).",
    "decision_label": "Final decision label (Altamente raccomandato / Quasi impossibile / ...).",
    "score": "Generic numeric score used in meta-portfolio.",

    # Structural fields
    "n_cities": "Number of cities for TSP instances.",
    "n_vars": "Number of variables for SAT instances.",
    "n_clauses": "Number of clauses for SAT instances.",
    "seed_param": "Seed grid parameter (e.g. param in {1,2,3}).",
    "seed_factor": "Seed grid factor (e.g. factor in {1,2,3}).",

    # Trace keys
    "U_values": "Optional full trace of U(t) along the history.",
    "kappa_values": "Optional full trace of kappa(t) along the history.",
}


# --- Helper functions -----------------------------------------------------


def new_metrics(
    family_label: str = "",
    instance_label: str = "",
    problem_type: str = "",
) -> Dict[str, object]:
    """Create a fresh Loventre metrics dict with canonical keys.

    All canonical keys are present and initialised to None, except
    family_label / instance_label / problem_type which are set from
    the arguments (empty strings are normalised to None).

    This is the recommended starting point for new labs.
    """
    metrics: Dict[str, object] = {key: None for key in ALL_KEYS}
    metrics["family_label"] = family_label or None
    metrics["instance_label"] = instance_label or None
    metrics["problem_type"] = problem_type or None
    return metrics


def ensure_loventre_keys(raw: Mapping[str, object]) -> Dict[str, object]:
    """Return a copy of *raw* where all Loventre keys are present.

    - Existing keys are preserved as they are.
    - Missing canonical keys (ALL_KEYS) are added with value None.
    - Extra keys from *raw* are left untouched.

    This is useful to normalise older metrics dicts produced by
    different labs while converging on the canonical vocabulary.
    """
    metrics: Dict[str, object] = dict(raw)
    for key in ALL_KEYS:
        metrics.setdefault(key, None)
    return metrics


def update_inplace(
    metrics: MutableMapping[str, object],
    **updates: object,
) -> MutableMapping[str, object]:
    """Update *metrics* in-place with the given fields and return it.

    This is just a tiny convenience helper to allow patterns like:

        m = new_metrics(...)
        update_inplace(m, V0=V0, a_min=a_min, p_tunnel=p)

    The function does not restrict keys to the canonical set: if you use
    a non-canonical key, it will be added as well.
    """
    metrics.update(updates)
    return metrics


def describe_key(key: str) -> str:
    """Return a short human-readable description for *key*."""
    return METRIC_DOC.get(key, "No documentation available for this key.")


__all__ = [
    "CORE_KEYS",
    "TIME_KEYS",
    "HORIZON_KEYS",
    "META_KEYS",
    "STRUCTURAL_KEYS",
    "TRACE_KEYS",
    "ALL_KEYS",
    "METRIC_DOC",
    "new_metrics",
    "ensure_loventre_keys",
    "update_inplace",
    "describe_key",
]
'''


def main() -> None:
    root = Path(__file__).resolve().parents[1]
    scripts_dir = root / "scripts"
    scripts_dir.mkdir(exist_ok=True)

    target = root / "loventre_metrics_bus.py"
    if target.exists():
        existing = target.read_text(encoding="utf-8")
    else:
        existing = None

    if existing == MODULE_CONTENT:
        print("loventre_metrics_bus.py already up to date.")
    else:
        target.write_text(MODULE_CONTENT, encoding="utf-8")
        print("loventre_metrics_bus.py written/updated.")


if __name__ == "__main__":
    main()

