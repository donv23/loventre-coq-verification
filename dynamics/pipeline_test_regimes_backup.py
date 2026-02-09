from flow_analyzer.core.transitions import apply_algorithm_a, apply_algorithm_b
from flow_analyzer.core.state import State
from flow_analyzer.pipeline.pipeline import FlowPipeline
from flow_analyzer.multiscale.trajectory_analyzer import analyze_trajectory


def main():
    # Stato iniziale con history
    initial_state = State(data={"value": 0, "history": [0]})

    # Pipeline con Algorithm A e Algorithm B
    pipeline = FlowPipeline(
        transitions=[
            apply_algorithm_a(param=2),
            apply_algorithm_b(factor=3),
        ]
    )

    # Esecuzione pipeline
    final_state, metrics = pipeline.run(initial_state)

    print("Stato finale:")
    print(final_state)

    print("Metriche finali:")
    print(metrics)

    # Secondo algoritmo: analisi della traiettoria
    profile = analyze_trajectory(final_state, metrics)

    print("Profilo del flusso:")
    print(profile)


if __name__ == "__main__":
    main()
