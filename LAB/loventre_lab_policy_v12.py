#!/usr/bin/env python3
# -*- coding: utf-8 -*-

"""
loventre_lab_policy_v12.py
------------------------------------------------
Strato di policy sperimentale V12.

Regole semplici:
 - se bus_state = BLACKHOLE-ish  → NO_GO_ZONE
 - se bus_state = P_ACC-ish      → MOVE_FORWARD
 - se bus_state = SAFE-ish       → CONTINUE
 - altrimenti                    → WAIT_AND_MONITOR

Non fa parte del core.
"""

def suggest_lab_policy_v12(kappa_eff=None, entropy_eff=None, bus_state=None):
    """
    Suggerimento di policy locale sandbox.
    Non guarda tutto il dict ma solo il bus-state (passato dall'esterno).
    """
    if bus_state == "BLACKHOLE-ish":
        return {"policy_hint_v12": "NO_GO_ZONE"}

    if bus_state == "P_ACC-ish":
        return {"policy_hint_v12": "MOVE_FORWARD"}

    if bus_state == "SAFE-ish":
        return {"policy_hint_v12": "CONTINUE"}

    return {"policy_hint_v12": "WAIT_AND_MONITOR"}


def demo():
    print("=== DEMO V12 LAB POLICY ===")
    test_states = ["SAFE-ish", "P_ACC-ish", "BLACKHOLE-ish", None]

    for state in test_states:
        label = state if state is not None else "None"
        print(f"bus={label:>13} →", suggest_lab_policy_v12(bus_state=state))


if __name__ == "__main__":
    demo()

