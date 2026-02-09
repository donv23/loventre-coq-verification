from .transitions import apply_transition

class FlowEngine:
    """
    Minimal engine that applies a sequence of transitions to the state.
    """
    def __init__(self, transitions=None):
        self.transitions = transitions if transitions is not None else []

    def step(self, state):
        new_state = state.copy()
        for t in self.transitions:
            new_state = apply_transition(new_state, t)
        return new_state
