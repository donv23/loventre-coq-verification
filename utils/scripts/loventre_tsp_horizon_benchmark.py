#!/usr/bin/env python3
"""
loventre_tsp_horizon_benchmark.py

Benchmark TSP sintetico per Loventre Horizon Oracle.

- Genera istanze TSP con N città (coordinate 2D random).
- Risolve ogni istanza con una brute force controllata (per N <= 10).
- Estrae semplici feature (lunghezza tour ottimo, scala media delle distanze, dispersione).
- Mappa queste feature in un core Loventre sintetico usando una calibrazione ispirata ai demo:
    * PRECRITICAL   ~ DEMO CASE 3 (scenario manovrabile)
    * SUPERCRITICAL ~ DEMO CASE 1 (buco nero Loventre)
    * INTERMEDIATE  ~ valori intermedi
- Esegue la pipeline Loventre Horizon Oracle:

    _snapshot_loventre_core_baseline
    → append_schwarzschild_layer_to_metrics
    → append_hawking_layer_to_metrics   (incluso canale UV)
    → append_planck_layer_to_metrics
    → apply_policy_bridge_to_metrics
    → append_policy_bridge_to_metrics

- Stampa un mini-report per istanza e un riepilogo statistico finale.
"""

import sys
import math
import random
import itertools
import statistics
import pathlib


# ---------------------------
# Import del meta–engine
# ---------------------------

def import_meta_engine():
    """Aggancia la root del progetto e importa loventre_meta_decision_engine."""
    root = pathlib.Path(__file__).resolve().parents[1]
    if str(root) not in sys.path:
        sys.path.insert(0, str(root))
    try:
        import loventre_meta_decision_engine as lmd  # type: ignore
    except Exception as e:
        print("[ERROR] Impossibile importare loventre_meta_decision_engine:", e)
        print("sys.path attuale:")
        for p in sys.path:
            print("  -", p)
        sys.exit(1)
    return lmd


# ---------------------------
# TSP sintetico: generazione + brute force
# ---------------------------

def generate_tsp_coords(num_cities: int, seed: int = None):
    """Genera num_cities punti 2D uniformi in [0,1]x[0,1]."""
    rng = random.Random(seed)
    coords = [(rng.random(), rng.random()) for _ in range(num_cities)]
    return coords


def euclidean_distance(a, b) -> float:
    return math.hypot(a[0] - b[0], a[1] - b[1])


def compute_distance_matrix(coords):
    n = len(coords)
    dmat = [[0.0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            d = euclidean_distance(coords[i], coords[j])
            dmat[i][j] = d
            dmat[j][i] = d
    return dmat


def tour_length(order, dmat) -> float:
    """Lunghezza di un tour che visita le città in ordine e ritorna allo start."""
    total = 0.0
    n = len(order)
    for i in range(n):
        a = order[i]
        b = order[(i + 1) % n]
        total += dmat[a][b]
    return total


def brute_force_tsp(dmat):
    """
    Risolve TSP con brute force fissando la città 0 come start.
    Per N=10 abbiamo 9! ≈ 362k tour, il che è gestibile.
    Restituisce (best_length, best_order).
    """
    n = len(dmat)
    if n > 10:
        raise ValueError("brute_force_tsp pensato per N <= 10")

    cities = list(range(n))
    start = 0
    others = cities[1:]
    best_len = float("inf")
    best_order = None

    for perm in itertools.permutations(others):
        order = (start,) + perm
        length = tour_length(order, dmat)
        if length < best_len:
            best_len = length
            best_order = order

    return best_len, best_order


# ---------------------------
# Mappatura TSP → core Loventre
# ---------------------------

def build_loventre_core_from_tsp(instance_id: str, coords, dmat, best_length: float):
    """
    Costruisce un core Loventre sintetico a partire da un'istanza TSP.

    NON usiamo formule interne del motore, ma una calibrazione dimostrativa:
    - calcoliamo un difficulty_factor,
    - se è basso → scenario precritico manovrabile (tipo DEMO CASE 3),
    - se è alto  → scenario supercritico (tipo DEMO CASE 1),
    - altrimenti → scenario intermedio.
    """
    n = len(coords)

    # Distanze base
    all_dists = [dmat[i][j] for i in range(n) for j in range(n) if i < j]
    mean_dist = statistics.mean(all_dists)
    std_dist = statistics.pstdev(all_dists)

    mean_per_city = best_length / n
    # difficulty_factor < 1 = tour "più corto" della scala media
    difficulty_factor = mean_per_city / (mean_dist + 1e-9)

    # Soglie empiriche sull’intervallo visto (~0.48–0.63)
    # diff < 0.53  → precritico manovrabile
    # diff > 0.60  → supercritico
    # else         → intermedio
    if difficulty_factor < 0.53:
        regime_tag = "PRECRITICAL"
        # Ispirato al DEMO CASE 3 – scenario manovrabile / precritico
        kappa_eff = 0.6
        entropy_eff = 1.4
        V0 = 1.8
        p_tunnel = 0.18
        mass_mean = 0.9
        chi = 0.22
        risk_index = 1.5
    elif difficulty_factor > 0.60:
        regime_tag = "SUPERCRITICAL"
        # Ispirato al DEMO CASE 1 – buco nero Loventre
        kappa_eff = 0.9
        entropy_eff = 1.8
        V0 = 2.5
        p_tunnel = 0.22
        mass_mean = 1.3
        chi = 0.35
        risk_index = 2.1
    else:
        regime_tag = "INTERMEDIATE"
        # Valori intermedi tra i due casi
        kappa_eff = 0.75
        entropy_eff = 1.6
        V0 = 2.1
        p_tunnel = 0.20
        mass_mean = 1.1
        chi = 0.30
        risk_index = 1.8

    metrics = {
        "instance_id": instance_id,
        "instance_label": f"TSP-{n}-citta benchmark ({regime_tag})",
        "tsp_num_cities": n,
        "tsp_best_length": best_length,
        "tsp_mean_dist": mean_dist,
        "tsp_std_dist": std_dist,
        "tsp_difficulty_factor": difficulty_factor,
        "tsp_regime_tag": regime_tag,
        # Core Loventre sintetico calibrato sui demo
        "kappa_eff": kappa_eff,
        "entropy_eff": entropy_eff,
        "V0": V0,
        "p_tunnel": p_tunnel,
        "mass_mean": mass_mean,
        "chi": chi,
        "risk_index": risk_index,
    }
    return metrics


# ---------------------------
# Pipeline Loventre Horizon Oracle
# ---------------------------

def run_horizon_pipeline(lmd, metrics: dict) -> dict:
    """
    Esegue i layer principali del meta–engine Loventre Horizon Oracle
    sul dict metrics fornito.
    """
    # 1. Snapshot del core (se disponibile)
    if hasattr(lmd, "_snapshot_loventre_core_baseline"):
        try:
            metrics = lmd._snapshot_loventre_core_baseline(metrics)  # type: ignore[attr-defined]
        except Exception as e:
            print("[WARN] _snapshot_loventre_core_baseline ha sollevato un'eccezione:", repr(e))

    # 2. Schwarzschild layer
    if hasattr(lmd, "append_schwarzschild_layer_to_metrics"):
        try:
            metrics = lmd.append_schwarzschild_layer_to_metrics(metrics)  # type: ignore[attr-defined]
        except Exception as e:
            print("[WARN] append_schwarzschild_layer_to_metrics ha sollevato un'eccezione:", repr(e))

    # 3. Hawking + UV layer
    if hasattr(lmd, "append_hawking_layer_to_metrics"):
        try:
            metrics = lmd.append_hawking_layer_to_metrics(metrics)  # type: ignore[attr-defined]
        except Exception as e:
            print("[WARN] append_hawking_layer_to_metrics ha sollevato un'eccezione:", repr(e))

    # 4. Planck layer
    if hasattr(lmd, "append_planck_layer_to_metrics"):
        try:
            metrics = lmd.append_planck_layer_to_metrics(metrics)  # type: ignore[attr-defined]
        except Exception as e:
            print("[WARN] append_planck_layer_to_metrics ha sollevato un'eccezione:", repr(e))

    # 5. Policy Bridge
    if hasattr(lmd, "apply_policy_bridge_to_metrics"):
        try:
            metrics = lmd.apply_policy_bridge_to_metrics(metrics)  # type: ignore[attr-defined]
        except Exception as e:
            print("[WARN] apply_policy_bridge_to_metrics ha sollevato un'eccezione:", repr(e))

    if hasattr(lmd, "append_policy_bridge_to_metrics"):
        try:
            metrics = lmd.append_policy_bridge_to_metrics(metrics)  # type: ignore[attr-defined]
        except Exception as e:
            print("[WARN] append_policy_bridge_to_metrics ha sollevato un'eccezione:", repr(e))

    return metrics


# ---------------------------
# Utility per il report
# ---------------------------

def _g(m, key, default=None):
    return m.get(key, default)


def print_instance_summary(idx: int, metrics: dict):
    print("=" * 72)
    print(f"[TSP INSTANCE {idx}]")
    print(f"  tsp_num_cities       : {_g(metrics, 'tsp_num_cities')!r}")
    print(f"  tsp_best_length      : {_g(metrics, 'tsp_best_length')!r}")
    print(f"  tsp_difficulty_factor: {_g(metrics, 'tsp_difficulty_factor')!r}")
    print(f"  tsp_regime_tag       : {_g(metrics, 'tsp_regime_tag')!r}")
    print(f"  risk_index           : {_g(metrics, 'risk_index')!r}")
    print(f"  schwarzschild_regime : {_g(metrics, 'schwarzschild_regime')!r}")
    print(f"  hawking_regime       : {_g(metrics, 'hawking_regime')!r}")
    print(f"  hawking_uv_phase     : {_g(metrics, 'hawking_uv_phase')!r}")
    print(f"  policy_strategy      : {_g(metrics, 'policy_strategy')!r}")
    print(f"  policy_energy        : {_g(metrics, 'policy_energy')!r}")
    comment = _g(metrics, "policy_comment")
    if comment:
        print("  policy_comment:")
        first_line = str(comment).splitlines()[0]
        print("   ", first_line)
    print()


def print_global_stats(results):
    """
    results: lista di dict metrics finali.
    """
    from collections import Counter

    total = len(results) if results else 1

    def pct(v):
        return 100.0 * v / total

    strategies = Counter(_g(m, "policy_strategy") for m in results)
    energies = Counter(_g(m, "policy_energy") for m in results)
    schw_regimes = Counter(_g(m, "schwarzschild_regime") for m in results)
    uv_phases = Counter(_g(m, "hawking_uv_phase") for m in results)
    tsp_tags = Counter(_g(m, "tsp_regime_tag") for m in results)

    # Matrice (tsp_regime_tag, policy_strategy)
    combo = Counter(( _g(m, "tsp_regime_tag"), _g(m, "policy_strategy")) for m in results)

    print("=" * 72)
    print("RIEPILOGO GLOBALE TSP + LOVENTRE HORIZON ORACLE")
    print("=" * 72)
    print("Tag regime TSP sintetico:")
    for k, v in tsp_tags.items():
        print(f"  {k!r}: {v} ({pct(v):.1f}%)")
    print()
    print("Strategie di policy:")
    for k, v in strategies.items():
        print(f"  {k!r}: {v} ({pct(v):.1f}%)")
    print()
    print("Livelli di energia:")
    for k, v in energies.items():
        print(f"  {k!r}: {v} ({pct(v):.1f}%)")
    print()
    print("Regimi Schwarzschild:")
    for k, v in schw_regimes.items():
        print(f"  {k!r}: {v} ({pct(v):.1f}%)")
    print()
    print("Fasi Hawking UV:")
    for k, v in uv_phases.items():
        print(f"  {k!r}: {v} ({pct(v):.1f}%)")
    print()
    print("Matrice (tsp_regime_tag, policy_strategy):")
    for (tag, strat), v in combo.items():
        print(f"  ({tag!r}, {strat!r}): {v} ({pct(v):.1f}%)")
    print()
    print("Numero totale di istanze analizzate:", len(results))
    print("=" * 72)


# ---------------------------
# MAIN
# ---------------------------

def main():
    # Parametri benchmark
    NUM_INSTANCES = 10    # puoi alzare a 30/50 se vuoi più statistica
    NUM_CITIES = 10
    BASE_SEED = 12345

    print("================================================================")
    print(" LOVENTRE TSP HORIZON BENCHMARK")
    print("================================================================")
    print(f"  Numero istanze TSP  : {NUM_INSTANCES}")
    print(f"  Numero città per TSP: {NUM_CITIES}")
    print("  Nota: brute force TSP usata per N <= 10.")
    print("================================================================\n")

    lmd = import_meta_engine()
    results = []

    for i in range(NUM_INSTANCES):
        inst_id = f"TSP-DEMO-{i+1}"
        seed = BASE_SEED + i

        # 1) Genera TSP
        coords = generate_tsp_coords(NUM_CITIES, seed=seed)
        dmat = compute_distance_matrix(coords)

        # 2) Risolvi TSP (brute force controllata)
        try:
            best_length, best_order = brute_force_tsp(dmat)
        except ValueError as e:
            print("[ERROR] brute_force_tsp:", e)
            return

        # 3) Costruisci core Loventre sintetico calibrato
        core_metrics = build_loventre_core_from_tsp(inst_id, coords, dmat, best_length)

        # 4) Esegui pipeline Horizon
        metrics = run_horizon_pipeline(lmd, dict(core_metrics))

        # 5) Stampa riepilogo per istanza
        print_instance_summary(i + 1, metrics)
        results.append(metrics)

    # 6) Riepilogo globale
    print_global_stats(results)


if __name__ == "__main__":
    main()

