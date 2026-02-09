"""
LOVENTRE ENGINE — V33 SAFE ENVELOPE
-----------------------------------
Versione indipendente e non invasiva del core.

Obiettivi:
 - Applicare un involucro decisionale attorno al motore attuale
 - Etichettare SAFE in tre modalità:
      SAFE_STRICT
      SAFE_TUNNELED
      SAFE_TEST_EXPLORATION
 - Imporre un “paracadute” automatico quando si entra in BLACKHOLE
 - NON modificare V13–V32
 - Nessun impatto sul Coq canonico

Regola generale:
   decision SAFE ← motore core
   ma viene reinterpretata entro una barriera temporale
"""

from typing import Dict, Any, Tuple


# 🎯 Etichette possibili
SAFE_STRICT = "SAFE_STRICT"
SAFE_TUNNELED = "SAFE_TUNNELED"
SAFE_TEST_EXPLORATION = "SAFE_TEST_EXPLORATION"
BH_TRANSIENT = "BLACKHOLE_TRANSIENT"


def classify_safe_envelope(kappa: float,
                           risk_index: float,
                           envelope: float = 1.0,
                           tunnel_width: float = 2.0) -> str:
    """
    Classificatore SAFE Envelope V33.

    envelope      → soglia normalizzata sotto cui si rimane in zona STRONG
    tunnel_width  → margine in cui consentiamo SAFE con dispersione controllata
    """
    if risk_index <= envelope:
        return SAFE_STRICT
    if risk_index <= envelope + tunnel_width:
        return SAFE_TUNNELED
    return SAFE_TEST_EXPLORATION


def interpret_with_envelope(base_state: Dict[str, Any],
                            envelope: float = 1.0,
                            tunnel_width: float = 2.0,
                            return_to_strict_after: int = 1) -> Dict[str, Any]:
    """
    Reinterpreta la decisione globale fornita dal core V32/V13.

    Se BLACKHOLE:
        - Rietichetta come BLACKHOLE_TRANSIENT
        - Non modifica i numeri
        - Invia paracadute SEMANTICO
    """
    state = dict(base_state)  # copia difensiva

    decision = state.get("loventre_global_decision")
    risk = state.get("risk_index", 0.0)

    # Caso BLACKHOLE → non cambiato numericamente, ma semanticamente
    if decision == "BLACKHOLE":
        state["envelope_tag"] = BH_TRANSIENT
        state["recovery_hint"] = (
            "Transient BH event detected. "
            "Switching to SAFE_STRICT recommended on next state."
        )
        state["auto_reentry"] = return_to_strict_after
        return state

    # Caso SAFE → interpreta via barriera
    safe_tag = classify_safe_envelope(
        kappa=state.get("kappa_eff", 0.0),
        risk_index=risk,
        envelope=envelope,
        tunnel_width=tunnel_width,
    )

    state["envelope_tag"] = safe_tag
    state["recovery_hint"] = None
    state["auto_reentry"] = 0
    return state


def run_safe_envelope_over_series(series: Tuple[Dict[str, Any], ...],
                                  envelope: float = 1.0,
                                  tunnel_width: float = 2.0) -> Tuple[Dict[str, Any], ...]:
    """
    Applica il reinterpretatore V33 a una serie di snapshot del motore core.
    Utile per oscillazioni brevi e per testare ritorni a SAFE_STRICT.
    """
    results = []
    for st in series:
        results.append(
            interpret_with_envelope(st, envelope=envelope, tunnel_width=tunnel_width)
        )
    return tuple(results)


if __name__ == "__main__":
    print("LOVENTRE V33 Envelope Module Loaded.")
    demo = {
        "loventre_global_decision": "SAFE",
        "risk_index": 1.4,
        "kappa_eff": 0.7,
    }
    print(interpret_with_envelope(demo))

