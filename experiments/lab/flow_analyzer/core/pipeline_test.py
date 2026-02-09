import os
import sys

# Percorso della cartella in cui si trova questo file (loventre_engine_clean_seed)
CURRENT_DIR = os.path.dirname(os.path.abspath(__file__))

# Percorso della cartella "flow_analyzer" dentro al progetto
FLOW_ANALYZER_DIR = os.path.join(CURRENT_DIR, "flow_analyzer")

# Aggiungiamo "flow_analyzer" al path di ricerca moduli
if FLOW_ANALYZER_DIR not in sys.path:
    sys.path.insert(0, FLOW_ANALYZER_DIR)

# Ora possiamo importare direttamente da "core" e "pipeline"
from core.transitions import apply_algorithm_a, apply_algorithm_b
from core.state import State
from pipeline.pipeline import FlowPipeline


def main():
    # Stato iniziale
    initial_state = State(data={"value": 0})

    # Pipeline con Algorithm A e Algorithm B
    pipeline = FlowPipeline(
        transitions=[
            apply_algorithm_a(param=2),
            apply_algorithm_b(factor=3),
        ]
    )

    # Esecuzione pipeline
    final_state = pipeline.run(initial_state)

    print("Risultato della pipeline:")
    print(final_state)


if __name__ == "__main__":
    main()
