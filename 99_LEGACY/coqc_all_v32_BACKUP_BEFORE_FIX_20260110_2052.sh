#!/bin/bash

echo "=== LOVENTRE V32 — FULL DEPENDENCY BUILD START ==="

# 0 — CANON v3
echo "[0] Build CANON v3 (coqc_all_v3.sh)"
bash coqc_all_v3.sh || exit 1

# A — SAFE + LMetrics chain
echo "[A] SAFE + LMetrics chain"
coqc Loventre_Structural_Sensitivity.v || exit 1
coqc Loventre_SAFE_Classifier.v || exit 1
coqc Loventre_LMetrics_Structure.v || exit 1

# B — Complexity / Noise / Class
echo "[B] Complexity/Noise/Class chain"
coqc Loventre_Complexity_Noise_Stability.v || exit 1
coqc Loventre_Class_Noise_Alignment.v      || exit 1
coqc Loventre_Class_Noise_Separation.v     || exit 1

# C — JSON Bridge V32 (nuovi file!)
echo "[C] JSON Bridge / V32"
coqc Loventre_v32_JSON_Types.v          || exit 1
coqc Loventre_v32_JSON_Loader.v         || exit 1
coqc Loventre_v32_JSON_To_LMetrics.v    || exit 1
coqc Loventre_Witness_Loader.v          || exit 1

echo "=== LOVENTRE COQ V32 — BUILD OK ==="

