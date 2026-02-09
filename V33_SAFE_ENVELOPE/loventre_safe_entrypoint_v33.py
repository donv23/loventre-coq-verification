"""
loventre_safe_entrypoint_v33.py
Loventre Engine — SAFE ENVELOPE V33
Gennaio 2026

Espone:
 - wrap_safe_envelope_v33(raw)  → singolo step
 - interpret_with_envelope(**params) → usa global_decision
"""

from demo_seed_global_decision import run_case
from loventre_global_entrypoint import loventre_global_decide_with_policy


def wrap_safe_envelope_v33(raw):
    """
    Applica il SAFE ENVELOPE V33 a un dizionario V6/V32 (raw state)
    e ritorna un nuovo dizionario arricchito con SAFE tags.
    """
    # Copia superficiale
    out = dict(raw)

    gd = raw.get("loventre_global", {}).get("global_decision", "SAFE")

    if gd == "SAFE":
        kappa = raw.get("kappa_eff", 0.0)
        # Tag più severo se kappa molto alta (potenziale barriera)
        if kappa >= 2.0:
            tag = "SAFE_TUNNELED"
        else:
            tag = "SAFE_STRICT"
        recovery_hint = None
        auto_reentry = 0
    elif gd == "BLACKHOLE":
        tag = "BLACKHOLE_TRANSIENT"
        recovery_hint = (
            "Transient BH event detected. Switching to SAFE_STRICT recommended on next state."
        )
        auto_reentry = 1
    else:
        # fallback
        tag = "SAFE_STRICT"
        recovery_hint = None
        auto_reentry = 0

    out["envelope_tag"] = tag
    out["recovery_hint"] = recovery_hint
    out["auto_reentry"] = auto_reentry
    return out


def interpret_with_envelope(**kwargs):
    """
    Chiama global_decide e applica l'envelope V33
    """
    raw = loventre_global_decide_with_policy(**kwargs)
    return wrap_safe_envelope_v33(raw)


def main():
    print("\n===== LOVENTRE ENGINE — SAFE ENVELOPE V33 =====\n")
    TESTS = [
        {},
        {"kappa_eff": 0.1},
        {"kappa_eff": 0.8},
        {"kappa_eff": 2.5},
        {"kappa_eff": -0.2},
        {"kappa_eff": -1.1},
        {"kappa_eff": -3.3},
        {"entropy_eff": 4.0},
    ]
    for p in TESTS:
        print("=" * 80)
        print(f"CASE: {p or 'default'}")
        raw = loventre_global_decide_with_policy(**p)
        print("RAW:", raw)
        wrapped = wrap_safe_envelope_v33(raw)
        print("V33:", wrapped)
    print("\n===== END SAFE ENVELOPE V33 =====")


if __name__ == "__main__":
    main()

