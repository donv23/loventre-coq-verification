def main():
    # 1) Test Einstein–Loventre (geometry + time + energy + mass + horizon)
    run_block(
        "TEST EINSTEIN–LOVENTRE LAYERS",
        ["loventre_einstein_layers_test_lab.py"],
    )

    # 2) Meta-decisione completa su esempio_history.json
    run_block(
        "LOVENTRE META-DECISION CLI (esempio_history.json)",
        ["loventre_meta_decision_cli.py", "esempio_history.json"],
    )

    # 3) Global profile lab (seed grid + SAT/TSP + Schwarzschild atlas)
    run_block(
        "LOVENTRE GLOBAL PROFILE LAB",
        ["loventre_global_profile_lab.py"],
    )

    # 4) Debug Policy Bridge (strategia locale + meta_explanation tail)
    run_block(
        "DEBUG POLICY BRIDGE",
        ["scripts/debug_policy_bridge_example.py"],
    )

    # 5) Debug Hawking–Loventre (campi hawking_* + presenza nel testo)
    run_block(
        "DEBUG HAWKING PRESENCE",
        ["scripts/debug_hawking_presence.py"],
    )

    # 6) Lensing + meta-decision demo (geodesic corridor + policy bridge)
    run_block(
        "LOVENTRE LENSING + META-DECISION DEMO",
        ["loventre_lensing_meta_demo.py"],
    )

