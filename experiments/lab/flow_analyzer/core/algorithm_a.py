class AlgorithmA:
    """
    Minimal implementation of Algorithm A.
    This class applies a simple deterministic update rule.
    Future versions can override the `update_rule` method.
    """
    def __init__(self, param=1.0):
        self.param = param

    def update_rule(self, state):
        """
        Placeholder transformation:
        For each numeric value v in the state:
            v -> v + param
        """
        new_data = {}
        for k, v in state.data.items():
            if isinstance(v, (int, float)):
                new_data[k] = v + self.param
            else:
                new_data[k] = v
        return new_data

    def apply(self, state):
        from .state import State
        return State(self.update_rule(state))
