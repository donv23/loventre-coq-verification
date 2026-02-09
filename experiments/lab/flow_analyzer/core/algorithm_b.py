class AlgorithmB:
    """
    Algorithm B:
    Moltiplica il valore nello stato per un fattore.
    """

    def __init__(self, factor=3):
        self.factor = factor

    def apply(self, state):
        """
        Prende uno State, ne fa una copia, moltiplica data["value"]
        per il fattore e restituisce il nuovo stato.
        """
        # Copia dello stato per non modificarlo in-place
        new_state = state.copy()
        data = new_state.data

        if "value" in data:
            data["value"] = data["value"] * self.factor
        else:
            data["value"] = 0

        return new_state
