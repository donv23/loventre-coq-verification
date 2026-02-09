class State:
    """
    Minimal container for system state.
    Generic key-value store used by the Flow Engine.
    """
    def __init__(self, data=None):
        self.data = data if data is not None else {}

    def copy(self):
        return State(data=self.data.copy())

    def __repr__(self):
        return f"State({self.data})"


class InfoState:
    """
    Advanced state for Loventre Flow Analyzer (future use).
    Holds structured components: x, n, t, meta.
    """
    def __init__(self, x, n, t=0, meta=None):
        self.x = x
        self.n = n
        self.t = t
        self.meta = meta or {}

    def as_dict(self):
        return {
            "x": self.x,
            "n": self.n,
            "t": self.t,
            "meta": self.meta
        }

    def __repr__(self):
        return f"InfoState(x={self.x}, n={self.n}, t={self.t}, meta={self.meta})"
