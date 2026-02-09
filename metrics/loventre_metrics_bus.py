"""
loventre_metrics_bus.py
Loventre Metrics Bus — Terminal Regime + V6 MASS (non interferente)
Gennaio 2026
"""

from typing import Dict, Any

# Importiamo il nuovo layer mass v6 (safe, annotativo)
try:
    from metrics.loventre_mass_layer_v6 import compute_mass_v6
except ImportError:
    # Modalità degradata ma non bloccante
    def compute_mass_v6(metrics: Dict[str, Any]) -> float:
        return 1.0


REQUIRED_KEYS = [
    'kappa_eff',
    'entropy_eff',
    'V0',
    'a_min',
    'p_tunnel',
    'P_success',
    'gamma_dilation',
    'time_regime',
    'mass_eff',
    'inertial_idx',
    'risk_index',
    'risk_class',
    'meta_label',
    'chi_compactness',
    'horizon_flag',
    'loventre_global_decision',
    'C_regime',
    'gct_barrier',
]


def ensure_loventre_keys(metrics: Dict[str, Any]) -> Dict[str, Any]:
    """
    Normalizza il bus inserendo tutti i campi previsti.
    Questo layer è NON distruttivo e non modifica esiti globali.

    Ora arricchito con:
      - massa_eff_v6 = compute_mass_v6(kappa, entropy)
      - inertial_idx e indicatori derivati
    """
    # Copia difensiva
    out = dict(metrics)

    # Base minima
    kappa = float(out.get("kappa_eff", 0.0) or 0.0)
    entropy = float(out.get("entropy_eff", 0.0) or 0.0)

    # MASS V6 — annotativa
    mass = compute_mass_v6({"kappa_eff": kappa, "entropy_eff": entropy})
    out["mass_eff"] = mass

    # Inertial index ~ |massa| * |kappa|
    out["inertial_idx"] = abs(mass * kappa)

    # Risk index = mappa semplice per ora
    out["risk_index"] = abs(kappa) * (1 + entropy / 10)
    out["risk_class"] = "LOW" if out["risk_index"] < 1 else "HIGH"

    # Meta label provvisoria (v6 prelim)
    out["meta_label"] = "meta_v6_seed"

    # Placeholder neutri (Terminal Regime)
    out.setdefault("chi_compactness", None)
    out.setdefault("horizon_flag", None)
    out.setdefault("C_regime", "undefined")
    out.setdefault("gct_barrier", None)

    # Trascrizione della decisione snapshot come campo canonico
    global_info = out.get("loventre_global", {})
    out["loventre_global_decision"] = global_info.get("global_decision")
    out["loventre_global_color"] = global_info.get("global_color")
    out["loventre_global_score"] = global_info.get("global_score")

    # Completamento chiavi
    for key in REQUIRED_KEYS:
        out.setdefault(key, None)

    return out

