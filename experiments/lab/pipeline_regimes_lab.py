"""
pipeline_regimes_lab.py

Esplora la griglia (param, factor) su history corta, con:
- metriche 1D,
- analisi multicanale,
- classificazione Pattern C,
- e una prima stima di "tempo interno" short (internal_time_short)
  + classificazione time_regime_short (euclidean / threshold / hyperbolic / mixed).

L'idea:
- internal_time_short dipende da curvatura ed entropia della traiettoria corta,
  scalate rispetto alla lunghezza effettiva della history;
- time_regime_short è derivato simbolicamente dall'etichetta Pattern C:
  regular -> time_euclidean
  geometric_precritical -> time_threshold
  fully_critical -> time_hyperbolic
  altri -> time_mixed
"""

from flow_analyzer.core.transitions import apply_algorithm_a, apply_algorithm_b
from flow_analyzer.core.state import State
from flow_analyzer.pipeline.pipeline import FlowPipeline
from flow_analyzer.multiscale.trajectory_analyzer import analyze_trajectory
from multichannel_patterns import analyze_state_multichannel
from pattern_classifier import analyze_configuration_pattern


def safe_float(x, default=0.0):
    """Converte in float in modo sicuro, evitando crash su None / valori strani."""
    try:
        return float(x)
    except (TypeError, ValueError):
        return default


def compute_internal_time_short(
    profile,
    history_length,
    curvature_ref=1.0,
    entropy_ref=1.0,
    a=0.5,
    b=0.5,
):
    """
    Stima del "tempo interno" sulla history corta.

    - profile: dizionario prodotto da analyze_trajectory(...)
      da cui estraiamo almeno:
        profile["curvature"], profile["entropy"] se presenti.
    - history_length: numero di punti nella history (lunghezza effettiva).

    Formula (semplificata):
      curv = profile.curvature
      entr = profile.entropy

      k_norm = curv / (curvature_ref + |curv|)
      h_norm = entr / (entropy_ref + |entr|)

      time_density = 1 + a * k_norm + b * h_norm

      internal_time_short = history_length * time_density

    In regioni poco curve / poco entropiche, time_density ~ 1
    e quindi il tempo interno è quasi lineare.
    In regioni critiche, time_density cresce e pochi passi
    producono molto "tempo interno".
    """
    if history_length <= 0:
        return 0.0

    curvature = safe_float(profile.get("curvature"), 0.0)
    entropy = safe_float(profile.get("entropy"), 0.0)

    k_denom = curvature_ref + abs(curvature)
    h_denom = entropy_ref + abs(entropy)

    k_norm = curvature / k_denom if k_denom != 0.0 else 0.0
    h_norm = entropy / h_denom if h_denom != 0.0 else 0.0

    time_density = 1.0 + a * k_norm + b * h_norm
    internal_time = history_length * time_density

    return internal_time


def classify_time_regime_short_from_config(config_profile):
    """
    Regime temporale short derivato dalla configurazione Pattern C.

    - regular_configuration               -> time_euclidean
    - geometric_precritical_configuration -> time_threshold
    - fully_critical_configuration        -> time_hyperbolic
    - altrimenti                          -> time_mixed
    """
    label = config_profile.get("configuration_label")

    if label == "regular_configuration":
        return "time_euclidean"
    if label == "geometric_precritical_configuration":
        return "time_threshold"
    if label == "fully_critical_configuration":
        return "time_hyperbolic"

    return "time_mixed"


def run_experiment(param, factor):
    # Stato iniziale con history
    initial_state = State(data={"value": 0, "history": [0]})

    # Pipeline con Algorithm A e Algorithm B
    pipeline = FlowPipeline(
        transitions=[
            apply_algorithm_a(param=param),
            apply_algorithm_b(factor=factor),
        ]
    )

    # Esecuzione pipeline
    final_state, metrics = pipeline.run(initial_state)

    # Secondo algoritmo: analisi della traiettoria 1D
    profile = analyze_trajectory(final_state, metrics)

    # Estrazione sicura del value finale, history e channels
    data = getattr(final_state, "data", {})
    value = None
    history = None
    channels = None
    channels_spread = None
    history_length = 0

    if isinstance(data, dict):
        value = data.get("value")
        history = data.get("history")
        channels = data.get("channels")

        if isinstance(history, list):
            history_length = len(history)

        if isinstance(channels, list) and len(channels) >= 1:
            try:
                channels_spread = max(channels) - min(channels)
            except TypeError:
                channels_spread = None

    print("--------------------------------------------------")
    print(f"param = {param}, factor = {factor}")
    print(f"  value finale    : {value}")
    print(f"  metriche 1D     : {metrics}")
    print(f"  regime 1D       : {profile.get('regime')}")
    print(f"  history_tail    : {profile.get('history_tail')}")
    print(f"  history_length  : {history_length}")
    print(f"  notes           : {profile.get('notes')}")
    print(f"  channels_finali : {channels}")
    print(f"  channels_spread : {channels_spread}")

    # --- Analisi multicanale sullo state finale ---
    multichannel_profile = analyze_state_multichannel(
        state=final_state,
        window_size=3,
        stride=1,
        spread_threshold=2.0,  # soglia per high_spread nel profilo multicanale
    )

    print("  [MULTICHANNEL]")
    print(f"    regime_multichannel      : {multichannel_profile['regime_multichannel']}")
    print(f"    is_multichannel_critical : {multichannel_profile['is_multichannel_critical']}")
    print(f"    metrics_multichannel     : {multichannel_profile['metrics']}")
    print(f"    window_size              : {multichannel_profile['window_size']}")
    print(f"    stride                   : {multichannel_profile['stride']}")

    # --- Algorithm C: classificazione di configurazione (Pattern C) ---
    config_profile = analyze_configuration_pattern(
        state=final_state,
        profile_1d=profile,
        multichannel_profile=multichannel_profile,
        local_small_threshold=2.0,
        local_high_threshold=5.0,
    )

    flags = config_profile.get("flags", {})
    is_fully_critical = flags.get("is_fully_critical")
    has_geometric_precritical = flags.get("has_geometric_precriticality")
    is_regular = flags.get("is_regular")

    print("  [PATTERN C]")
    print(f"    configuration_label      : {config_profile.get('configuration_label')}")
    print(f"    is_fully_critical        : {is_fully_critical}")
    print(f"    has_geometric_precritical: {has_geometric_precritical}")
    print(f"    is_regular               : {is_regular}")

    # --- TIME SHORT: tempo interno e regime temporale locale ---
    internal_time_short = compute_internal_time_short(profile, history_length)
    time_regime_short = classify_time_regime_short_from_config(config_profile)

    print("  [TIME SHORT]")
    print(f"    internal_time_short      : {internal_time_short}")
    print(f"    time_regime_short        : {time_regime_short}")
    print()


def main():
    print("=== Esplorazione regimi (param, factor) con analisi multicanale + Pattern C + Time ===")

    param_values = [1, 2, 3]
    factor_values = [1, 2, 3]

    for param in param_values:
        for factor in factor_values:
            run_experiment(param, factor)


if __name__ == "__main__":
    main()
