from flow_analyzer.core.transitions import apply_algorithm_a, apply_algorithm_b
from flow_analyzer.core.state import State
from flow_analyzer.pipeline.pipeline import FlowPipeline
from flow_analyzer.multiscale.trajectory_analyzer import analyze_trajectory
from multichannel_patterns import analyze_state_multichannel


def safe_float(x, default=0.0):
    """Converte in float in modo sicuro, evitando crash su None / valori strani."""
    try:
        return float(x)
    except (TypeError, ValueError):
        return default


def compute_internal_time_long(
    profile,
    history_length,
    curvature_ref=1.0,
    entropy_ref=1.0,
    a=0.5,
    b=0.5,
):
    """
    Stima del "tempo interno" sulla history lunga.

    È la versione long della stessa idea usata in pipeline_regimes_lab
    per internal_time_short:

      curv = profile.curvature
      entr = profile.entropy

      k_norm = curv / (curvature_ref + |curv|)
      h_norm = entr / (entropy_ref + |entr|)

      time_density = 1 + a * k_norm + b * h_norm

      internal_time_long = history_length * time_density

    In regioni poco curve / poco entropiche, time_density ~ 1
    e quindi il tempo interno lungo è quasi proporzionale al numero di passi.
    In regioni critiche, time_density cresce e una history lunga
    produce un "tempo interno" molto più grande rispetto al caso regolare.
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


def classify_time_regime_long_from_params(
    param: int,
    factor: int,
    is_multichannel_critical: bool,
) -> str:
    """
    Regime temporale lungo, coerente con la tabella di critical_signature_lab:

      - se multi_critical_long è False                  -> time_euclidean
      - se multi_critical_long è True e
          (param,factor) in { (1,2), (2,2), (3,1) }     -> time_threshold
      - se multi_critical_long è True e
          (param,factor) in { (2,3), (3,2), (3,3) }     -> time_hyperbolic
      - altrimenti                                      -> time_mixed

    Nota:
    - (1,1) e (2,1) sono regolari anche su history lunga (non critici);
    - (1,2), (2,2), (3,1) sono pre-critici dal punto di vista temporale;
    - (2,3), (3,2), (3,3) sono i seed pienamente critici (NP-like) a lunga scala.
    """
    if not is_multichannel_critical:
        return "time_euclidean"

    precritical_set = {(1, 2), (2, 2), (3, 1)}
    fully_critical_set = {(2, 3), (3, 2), (3, 3)}

    key = (param, factor)

    if key in precritical_set:
        return "time_threshold"
    if key in fully_critical_set:
        return "time_hyperbolic"

    return "time_mixed"


def run_iterated_experiment(
    param: int,
    factor: int,
    iterations: int,
    spread_threshold: float = 2.0,
    verbose: bool = True,
):
    """
    Esegue la pipeline per un certo numero di iterazioni, riapplicando
    sempre la stessa pipeline sullo stato aggiornato, in modo da
    costruire una history lunga.

    Ritorna un dizionario di riepilogo con:
    - regime 1D,
    - regime multicanale,
    - flag di criticità multicanale,
    - channels_spread finale,
    - internal_time_long,
    - time_regime_long.
    """
    # Stato iniziale con history
    state = State(data={"value": 0, "history": [0]})

    # Pipeline con Algorithm A e Algorithm B
    pipeline = FlowPipeline(
        transitions=[
            apply_algorithm_a(param=param),
            apply_algorithm_b(factor=factor),
        ]
    )

    # Iterazioni successive: ciascuna run aggiorna lo stato e la history
    metrics = {}
    for _ in range(iterations):
        state, metrics = pipeline.run(state)

    # Analisi 1D sulla history lunga
    profile_1d = analyze_trajectory(state, metrics)

    # Estrazione sicura dei dati finali
    data = getattr(state, "data", {})
    value = None
    history = []
    channels = None

    if isinstance(data, dict):
        value = data.get("value")
        history = data.get("history", [])
        channels = data.get("channels")

    if not isinstance(history, list):
        history = []

    history_length = len(history)
    history_tail = history[-10:] if history_length > 10 else history

    # Mini-metrica locale sui canali finali
    channels_spread = None
    if isinstance(channels, (list, tuple)) and len(channels) > 0:
        try:
            c_min = min(channels)
            c_max = max(channels)
            channels_spread = c_max - c_min
        except TypeError:
            channels_spread = None

    # Analisi multicanale sulla history lunga (terzo algoritmo)
    multichannel_profile = analyze_state_multichannel(
        state=state,
        window_size=3,
        stride=1,
        spread_threshold=spread_threshold,
    )

    is_mc_critical = multichannel_profile["is_multichannel_critical"]

    # --- TIME LONG: tempo interno e regime temporale lungo ---
    internal_time_long = compute_internal_time_long(profile_1d, history_length)
    time_regime_long = classify_time_regime_long_from_params(
        param=param,
        factor=factor,
        is_multichannel_critical=is_mc_critical,
    )

    if verbose:
        print("==================================================")
        print(f"[ITERATED] param = {param}, factor = {factor}, iterations = {iterations}")
        print(f"  value finale         : {value}")
        print(f"  history length       : {history_length}")
        print(f"  history tail (max 10): {history_tail}")
        print(f"  metriche 1D          : {metrics}")
        print(f"  regime 1D            : {profile_1d.get('regime')}")
        print(f"  history_tail_1D      : {profile_1d.get('history_tail')}")
        print(f"  notes_1D             : {profile_1d.get('notes')}")
        print(f"  channels_finali      : {channels}")
        print(f"  channels_spread      : {channels_spread}")
        print("  [MULTICHANNEL LONG HISTORY]")
        print(f"    regime_multichannel      : {multichannel_profile['regime_multichannel']}")
        print(f"    is_multichannel_critical : {is_mc_critical}")
        print(f"    metrics_multichannel     : {multichannel_profile['metrics']}")
        print(f"    window_size              : {multichannel_profile['window_size']}")
        print(f"    stride                   : {multichannel_profile['stride']}")
        print("  [TIME LONG HISTORY]")
        print(f"    internal_time_long       : {internal_time_long}")
        print(f"    time_regime_long         : {time_regime_long}")
        print()

    # Riepilogo sintetico per il chiamante
    summary = {
        "param": param,
        "factor": factor,
        "iterations": iterations,
        "value_final": value,
        "regime_1d": profile_1d.get("regime"),
        "regime_multichannel": multichannel_profile["regime_multichannel"],
        "is_multichannel_critical": is_mc_critical,
        "channels_spread": channels_spread,
        "internal_time_long": internal_time_long,
        "time_regime_long": time_regime_long,
    }
    return summary


def main():
    print("=== Esplorazione multicanale con history lunga (griglia param-factor) ===")

    param_values = [1, 2, 3]
    factor_values = [1, 2, 3]
    iterations = 10
    spread_threshold = 2.0

    summaries = []

    for param in param_values:
        for factor in factor_values:
            summary = run_iterated_experiment(
                param=param,
                factor=factor,
                iterations=iterations,
                spread_threshold=spread_threshold,
                verbose=True,
            )
            summaries.append(summary)

    # Riepilogo sintetico finale
    print("=== Riepilogo sintetico regimi (history lunga) ===")
    for s in summaries:
        print(
            f"(param={s['param']}, factor={s['factor']}) -> "
            f"1D={s['regime_1d']}, "
            f"multi={s['regime_multichannel']}, "
            f"multi_critical={s['is_multichannel_critical']}, "
            f"channels_spread={s['channels_spread']}, "
            f"time_long={s['time_regime_long']}"
        )


if __name__ == "__main__":
    main()
