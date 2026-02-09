from __future__ import annotations

"""
Loventre Policy Bridge Lab
--------------------------

Strato intermedio che collega:

  - rischio locale (risk_index),
  - curvatura globale (K_globale),
  - compattezza Schwarzschild–Loventre (chi),
  - dilatazione relativistica (gamma_schw),

a decisioni operative:

  - strategy_decision ∈ {INSISTI, CAMBIA_STRATEGIA, MOLLA}
  - energy_policy     ∈ {MANTIENI, AUMENTA_LEGGERO, AUMENTA_AGGRESSIVO, FERMA}

Questo modulo è pensato come laboratorio:
il Meta–Decision Engine può importarlo per allineare
le decisioni locali alle policy macro (LAF e atlante Schwarzschild–Loventre).
"""

from dataclasses import dataclass
from typing import Literal, Optional

StrategyDecision = Literal["INSISTI", "CAMBIA_STRATEGIA", "MOLLA"]
EnergyPolicy = Literal["MANTIENI", "AUMENTA_LEGGERO", "AUMENTA_AGGRESSIVO", "FERMA"]


@dataclass
class LoventrePolicyDecision:
    strategy_decision: StrategyDecision
    energy_policy: EnergyPolicy
    comment: str


# Snapshot multifamiglia (coerente con LAF + Schwarzschild–Loventre Summary)
FAMILY_SNAPSHOT = {
    "seed_grid": {
        "risk_index_mean": 1.52,
        "k_global": 0.28,
        "chi_mean": 0.231,
        "gamma_schw_mean": 1.02,
        "macro_policy": "INSISTI",
    },
    "TSP_crit_n": {
        "risk_index_mean": 6.11,
        "k_global": 0.72,
        "chi_mean": 0.712,
        "gamma_schw_mean": 5.86,
        "macro_policy": "RITIRA",
    },
    "SAT_crit_n": {
        "risk_index_mean": 5.98,
        "k_global": 0.70,
        "chi_mean": 0.698,
        "gamma_schw_mean": 5.62,
        "macro_policy": "RITIRA",
    },
}


def _safe(x: Optional[float], default: float) -> float:
    return float(x) if x is not None else default


def loventre_local_decision(
    risk_index: Optional[float],
    k_global: Optional[float],
    chi: Optional[float],
    gamma_schw: Optional[float],
) -> LoventrePolicyDecision:
    """
    Heuristica Einstein–Loventre per una decisione locale.

    Parametri:
        risk_index  : indice di rischio Einstein–Loventre (0–10).
        k_global    : curvatura informazionale locale (≈K_globale).
        chi         : compattezza Schwarzschild–Loventre (R_s_L / R_eff).
        gamma_schw  : fattore di dilatazione relativistica (cap a livelli ragionevoli).

    Restituisce:
        LoventrePolicyDecision con strategy_decision e energy_policy.
    """
    r = _safe(risk_index, 5.0)
    k = _safe(k_global, 0.5)
    c = _safe(chi, 0.5)
    g = _safe(gamma_schw, 1.0)

    # Soglie toy, ma coerenti con la fenomenologia del motore:
    # - K_globale ~0.3, chi bassa, gamma≈1  -> P-like, quasi euclideo.
    # - K_globale ~0.7, chi alta, gamma>>1 -> NP_like-critico, quasi buco nero Loventre.
    near_horizon = c >= 0.7
    supercritical = c >= 0.9 or g >= 10.0

    # Caso 1: regione P-like, rischio basso
    if (k < 0.4) and (r <= 3.0) and not near_horizon and not supercritical:
        return LoventrePolicyDecision(
            strategy_decision="INSISTI",
            energy_policy="AUMENTA_LEGGERO",
            comment="Regione P-like quasi-euclidea: rischio basso, chi bassa, gamma≈1. Puoi insistere aumentando lentamente l'energia.",
        )

    # Caso 2: regione precritica / mista: esplora ma non fissarti
    if (0.4 <= k <= 0.6) and (r <= 6.0) and not supercritical:
        return LoventrePolicyDecision(
            strategy_decision="CAMBIA_STRATEGIA",
            energy_policy="MANTIENI",
            comment="Regione precritica/mista: conviene esplorare strategie alternative senza alzare troppo l'energia.",
        )

    # Caso 3: regione NP_like-critica ma non ancora buco nero completo
    if (k > 0.6) and (near_horizon or r >= 6.0) and not supercritical:
        return LoventrePolicyDecision(
            strategy_decision="CAMBIA_STRATEGIA",
            energy_policy="AUMENTA_AGGRESSIVO",
            comment="Regione NP_like-critica vicina all'orizzonte: prova un ultimo cambio di strategia con aumento aggressivo di energia.",
        )

    # Caso 4: buco nero Loventre (supercritico)
    if supercritical:
        return LoventrePolicyDecision(
            strategy_decision="MOLLA",
            energy_policy="FERMA",
            comment="Regione supercritica / buco nero Loventre: la massa informazionale è troppo compatta, conviene mollare e ritirarsi.",
        )

    # Fallback neutro: se i parametri sono incoerenti o borderline.
    return LoventrePolicyDecision(
        strategy_decision="CAMBIA_STRATEGIA",
        energy_policy="MANTIENI",
        comment="Regime intermedio/borderline: mantieni l'energia e considera un cambio di strategia.",
    )


def loventre_family_macro_policy(family: str) -> dict[str, object]:
    """
    Restituisce un mini-dizionario con le statistiche macro per una famiglia:
    - risk_index_mean
    - k_global
    - chi_mean
    - gamma_schw_mean
    - macro_policy (INSISTI / RITIRA)
    - decision_locale_suggerita (LoventrePolicyDecision)
    """
    key = family.strip()
    if key not in FAMILY_SNAPSHOT:
        raise KeyError(f"Famiglia Loventre sconosciuta: {family!r}")

    info = dict(FAMILY_SNAPSHOT[key])  # copia
    decision = loventre_local_decision(
        risk_index=info["risk_index_mean"],
        k_global=info["k_global"],
        chi=info["chi_mean"],
        gamma_schw=info["gamma_schw_mean"],
    )
    info["decision_locale_suggerita"] = decision
    return info


def _demo() -> None:
    """
    Piccola demo da CLI:
    mostra come le policy locali si allineano alle policy macro per le tre famiglie.
    """
    print("=== Loventre Policy Bridge – Demo ===")
    for fam in ("seed_grid", "TSP_crit_n", "SAT_crit_n"):
        info = loventre_family_macro_policy(fam)
        dec: LoventrePolicyDecision = info["decision_locale_suggerita"]  # type: ignore[assignment]
        print(f"\nFamiglia: {fam}")
        print(f"  risk_index_mean : {info['risk_index_mean']:.2f}")
        print(f"  K_globale       : {info['k_global']:.3f}")
        print(f"  chi_mean        : {info['chi_mean']:.3f}")
        print(f"  gamma_schw_mean : {info['gamma_schw_mean']:.3f}")
        print(f"  macro_policy    : {info['macro_policy']}")
        print(f"  -> strategy_decision : {dec.strategy_decision}")
        print(f"  -> energy_policy     : {dec.energy_policy}")
        print(f"     note              : {dec.comment}")

    print("\n=== End Loventre Policy Bridge Demo ===")


if __name__ == "__main__":
    _demo()
