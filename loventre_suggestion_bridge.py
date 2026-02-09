#!/usr/bin/env python3
# -*- coding: utf-8 -*-

def loventre_suggest_action(metrics):
    try:
        V0 = float(metrics.get("V0", None))
        info = float(metrics.get("informational_potential", None))
        inertia = float(metrics.get("informational_inertia", None))
    except Exception:
        return {
            "suggestion": "INSUFFICIENT_DATA",
            "gravity": None,
            "class": "UNKNOWN",
            "phase": "UNDEF"
        }

    # Gravity scale
    gravity = max(0.0, 1.0 - inertia)

    # Classification
    if inertia < 0.10:
        cls = "SAFE"
        phase = "FLAT"
        suggestion = "INSISTI"
    elif inertia < 0.25:
        cls = "ACCESSIBLE"
        phase = "EASY"
        suggestion = "VALUTA"
    else:
        cls = "BLACK_HOLE"
        phase = "SCHWARZSCHILD"
        suggestion = "RITIRA"

    return {
        "suggestion": suggestion,
        "gravity": round(gravity, 3),
        "class": cls,
        "phase": phase
    }

