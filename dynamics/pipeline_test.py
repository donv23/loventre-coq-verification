from flow_analyzer.core.transitions import apply_algorithm_a, apply_algorithm_b
from flow_analyzer.core.state import State
from flow_analyzer.pipeline.pipeline import FlowPipeline
from flow_analyzer.multiscale.trajectory_analyzer import analyze_trajectory
from multichannel_patterns import analyze_state_multichannel
from pattern_classifier import analyze_configuration_pattern


CRITICAL_PARAM = 2
CRITICAL_FACTOR = 3


def main():
    print("=== Loventre Engine – Run ufficiale (regime critico di riferimento) ===")

    # Stato iniziale con history
    initial_state = State(data={"value": 0, "history": [0]})

    # Pipeline con Algorithm A e Algorithm B nel regime critico di riferimento
    pipeline = FlowPipeline(
        transitions=[
            apply_algorithm_a(param=CRITICAL_PARAM),
            apply_algorithm_b(factor=CRITICAL_FACTOR),
        ]
    )

    # Esecuzione pipeline
    final_state, metrics = pipeline.run(initial_state)

    # Estrazione sicura dei dati dallo state finale
    data = getattr(final_state, "data", {})
    value = None
    channels = None
    channels_spread = None

    if isinstance(data, dict):
        value = data.get("value")
        channels = data.get("channels")
        if isinstance(channels, list) and len(channels) >= 1:
            try:
                channels_spread = max(channels) - min(channels)
            except TypeError:
                channels_spread = None

    print("\nStato finale:")
    print(final_state)

    print("\nMetriche finali (1D):")
    print(metrics)

    # Profilo 1D (Secondo Algoritmo)
    profile_1d = analyze_trajectory(final_state, metrics)

    print("\n[FLOW 1D]")
    print(f"  value finale   : {value}")
    print(f"  regime 1D      : {profile_1d.get('regime')}")
    print(f"  history_tail   : {profile_1d.get('history_tail')}")
    print(f"  notes          : {profile_1d.get('notes')}")

    # Informazioni sui channels (geometria finale semplificata)
    print("\n[CHANNELS]")
    print(f"  channels_finali: {channels}")
    print(f"  channels_spread: {channels_spread}")

    # Analisi multicanale (Terzo Algoritmo – parte A: profilo multicanale)
    multichannel_profile = analyze_state_multichannel(
        state=final_state,
        window_size=3,
        stride=1,
        spread_threshold=2.0,  # stessa soglia usata nel laboratorio dei regimi
    )

    print("\n[MULTICHANNEL]")
    print(f"  regime_multichannel      : {multichannel_profile['regime_multichannel']}")
    print(f"  is_multichannel_critical : {multichannel_profile['is_multichannel_critical']}")
    print(f"  metrics_multichannel     : {multichannel_profile['metrics']}")
    print(f"  window_size              : {multichannel_profile['window_size']}")
    print(f"  stride                   : {multichannel_profile['stride']}")

    # Analisi di configurazione (Terzo Algoritmo – parte B: Pattern C)
    config_profile = analyze_configuration_pattern(
        state=final_state,
        profile_1d=profile_1d,
        multichannel_profile=multichannel_profile,
        local_small_threshold=2.0,
        local_high_threshold=5.0,
    )

    flags = config_profile.get("flags", {})
    is_fully_critical = flags.get("is_fully_critical")
    has_geometric_precritical = flags.get("has_geometric_precriticality")
    is_regular = flags.get("is_regular")

    print("\n[PATTERN C – CONFIGURAZIONE CRITICA]")
    print(f"  configuration_label      : {config_profile.get('configuration_label')}")
    print(f"  is_fully_critical        : {is_fully_critical}")
    print(f"  has_geometric_precritical: {has_geometric_precritical}")
    print(f"  is_regular               : {is_regular}")


if __name__ == "__main__":
    main()

