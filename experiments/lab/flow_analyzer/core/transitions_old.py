from .algorithm_a import AlgorithmA

def apply_transition(state, transition_fn):
    """
    Applies a single transition function to the State.
    A transition function receives and returns a State.
    """
    return transition_fn(state.copy())


def identity_transition(state):
    """
    Identity transition (does nothing).
    """
    return state


def apply_algorithm_a(param=1.0):
    """
    Wraps AlgorithmA inside a transition function
    compatible with FlowEngine.
    """
    algo = AlgorithmA(param=param)

    def transition(state):
        return algo.apply(state)

    return transition
