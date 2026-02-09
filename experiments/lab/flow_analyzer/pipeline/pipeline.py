from ..core.flow_engine import FlowEngine
from ..core.metrics import compute_all_metrics

class FlowPipeline:
    """
    Runs: state -> flow engine -> metrics
    """
    def __init__(self, transitions=None):
        self.engine = FlowEngine(transitions=transitions)

    def run(self, initial_state):
        final_state = self.engine.step(initial_state)
        metrics = compute_all_metrics(final_state)
        return final_state, metrics
