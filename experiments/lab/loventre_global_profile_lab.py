#!/usr/bin/env python3
"""
LOVENTRE ENGINE – Global seed profiles lab
==========================================

Script di laboratorio che calcola e stampa un profilo sintetico
dei 9 seed (param,factor) ∈ {1,2,3}² del motore Loventre, usando
l'analisi di istanza (curvatura, barriera, tunneling) e gli arricchimenti
tempo/massa già presenti in loventre_instance_analysis.

Non ha effetti sul nucleo del motore: si limita a costruire una history
toy per ogni seed, chiamare le funzioni pubbliche e stampare una tabella.
"""

from __future__ import annotations

from typing import Any, Dict, List

from loventre_instance_analysis import (
    analyze_instance,
    enrich_metrics_with_time_dilation,
    enrich_metrics_with_mass,
)


def build_history_for_seed(param: int, factor: int, n_steps: int = 24) -> List[Dict[str, float]]:
    """
    Costruisce una history toy {C,H} per il seed (param,factor).

    L'idea è:
      - C cresce moderatamente nel tempo, con un offset che dipende da param e factor;
      - H oscilla, con ampiezza legata a factor.
    """
    history: List[Dict[str, float]] = []

    base_C = 0.25 + 0.15 * (param - 1) + 0.05 * (factor - 1)
    base_H = 0.15 + 0.10 * (factor - 1)

    for t in range(n_steps):
        # Complessità che cresce
        C_t = base_C * (1.0 + 0.05 * t)
        # Entropia che oscilla ma con trend leggero
        H_t = base_H * (1.0 + 0.03 * ((t + param) % 7))
        history.append({"C": C_t, "H": H_t})

    return history


def analyze_seed(param: int, factor: int, energy: float, n_budget: int) -> Dict[str, Any]:
    """
    Analizza un seed (param,factor) costruendo una history toy,
    applicando analyze_instance + arricchimenti tempo/massa,
    e aggiungendo P_success e kappa_eff/entropy_eff sintetici.
    """
    history = build_history_for_seed(param, factor)

    metrics = analyze_instance(
        history,
        alpha=1.0,
        beta=1.0,
        G_L=1.0,
        lambda_L=0.1,
        V0=None,
        V0_quantile=0.85,
        E=energy,
    )

    # Probabilità di successo meta su N tentativi (approssimazione geometrica)
    p = float(metrics.get("p_tunnel", 0.0))
    if p <= 0.0:
        P_success = 0.0
    else:
        try:
            P_success = 1.0 - (1.0 - p) ** n_budget
        except OverflowError:
            # Se l'esponente va fuori scala, saturiamo a 1.0
            P_success = 1.0
    metrics["P_success"] = P_success

    # kappa_eff come media dei kappa_values (se disponibili)
    kappa_values = metrics.get("kappa_values")
    if isinstance(kappa_values, list) and kappa_values:
        kappa_eff = sum(float(k) for k in kappa_values) / float(len(kappa_values))
        metrics["kappa_eff"] = kappa_eff

    # entropy_eff come media degli H nella history
    H_values = [float(s.get("H", 0.0)) for s in history]
    if H_values:
        entropy_eff = sum(H_values) / float(len(H_values))
        metrics["entropy_eff"] = entropy_eff

    # Arricchimenti Loventre: dilatazione del tempo + massa informazionale
    metrics = enrich_metrics_with_time_dilation(
        metrics,
        gamma_cap=100.0,
        gamma_threshold_euclidean=2.0,
        gamma_threshold_hyperbolic=5.0,
    )
    metrics = enrich_metrics_with_mass(
        metrics,
        history,
        m0=1.0,
        w_C=1.0,
        w_H=0.5,
    )

    return metrics


def classify_region(metrics: Dict[str, Any]) -> str:
    """
    Restituisce una etichetta di regione compatta:

      - prima prova a usare 'region_label' (se presente),
      - altrimenti 'classification',
      - altrimenti 'default_region'.
    """
    region = metrics.get("region_label") or metrics.get("classification") or "default_region"
    return str(region)


def seed_profile_row(param: int, factor: int, metrics: Dict[str, Any]) -> str:
    """
    Costruisce una riga formattata per la tabella finale.
    """
    region = classify_region(metrics)

    p_tunnel = float(metrics.get("p_tunnel", 0.0))
    P_success = float(metrics.get("P_success", 0.0))
    V0_val = float(metrics.get("V0", 0.0))

    # kappa_eff / entropy_eff sintetici (se mancanti, fallback a 0.0)
    kappa_eff = float(metrics.get("kappa_eff", 0.0))
    entropy_eff = float(metrics.get("entropy_eff", 0.0))

    # Difficoltà inerziale se disponibile, altrimenti difficulty_index semplice
    difficulty_raw = metrics.get("inertial_difficulty_index", metrics.get("difficulty_index", 0.0))
    difficulty = float(difficulty_raw)

    # Flag P_like / NP_like (toy): P_success alta ~ P_like
    P_like_flag = P_success >= 0.5
    NP_like_flag = not P_like_flag

    row = (
        f"{param:5d} {factor:6d} "
        f"{region:9.9s} "
        f"{str(P_like_flag):5s} "
        f"{str(NP_like_flag):7s} "
        f"{kappa_eff:9.3f} "
        f"{entropy_eff:11.3f} "
        f"{V0_val:8.4f} "
        f"{p_tunnel:12.3e} "
        f"{P_success:11.3e} "
        f"{difficulty:11.3f}"
    )
    return row


def global_seed_profiles(energy: float, n_budget: int) -> None:
    """
    Calcola e stampa la tabella dei profili per tutti i 9 seed (param,factor).
    """
    print("===================================================================")
    print("=== PROFILI LOVENTRE – SEED (param,factor)                      ===")
    print("===================================================================")
    print(f"Energia E   : {energy}")
    print(f"N_budget    : {n_budget} tentativi meta per seed")
    print()
    print(
        "param factor region      P_like NP_like kappa_eff entropy_eff   V0       p_tunnel(E)   P_success   difficulty"
    )
    print("-" * 109)

    for param in (1, 2, 3):
        for factor in (1, 2, 3):
            metrics = analyze_seed(param, factor, energy=energy, n_budget=n_budget)
            row = seed_profile_row(param, factor, metrics)
            print(row)


def main() -> None:
    energy = 0.5
    n_budget = 1000
    global_seed_profiles(energy, n_budget)


if __name__ == "__main__":
    main()

