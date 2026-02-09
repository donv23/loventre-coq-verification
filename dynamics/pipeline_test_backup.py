from flow_analyzer.core.transitions import apply_algorithm_a
from flow_analyzer.core.state import State
from flow_analyzer.pipeline.pipeline import FlowPipeline

def main():
    # Stato iniziale
    initial_state = State(data={"value": 0})

    # Pipeline base
    pipeline = FlowPipeline(
        transitions=[
            apply_algorithm_a(param=2)
        ]
    )

    # Esecuzione pipeline
    final_state = pipeline.run(initial_state)

    print("Risultato della pipeline:")
    print(final_state)

if __name__ == "__main__":
    main()
