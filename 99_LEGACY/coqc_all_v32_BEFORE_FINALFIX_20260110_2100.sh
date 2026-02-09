#!/bin/bash

echo "=== LOVENTRE V32 — FULL DEPENDENCY BUILD START ==="

ROOT="."
COQC="coqc"

# 0. Build CANON v3 first
echo "[0] Build CANON v3 (coqc_all_v3.sh)"
bash coqc_all_v3.sh

echo "=== LOVENTRE COQ v3 — CANONICAL BUILD START ==="

# === CANON V3 CORE (pass-through, the script already handles order) ===
$COQC Loventre_Core_Classes.v
$COQC Loventre_Curvature_Base.v
$COQC Loventre_Curvature_Delta.v
$COQC Loventre_Curvature_Asymmetry.v
$COQC Loventre_Final_Theorem.v
$COQC Loventre_JSON_Bridge.v
$COQC Loventre_Curvature_Base.v

echo "=== LOVENTRE COQ v3 — BUILD OK (GREEN) ==="

echo "[A] SAFE + LMetrics chain"

# 1. Compile LMetrics STRUCTURE FIRST (prerequisite!)
$COQC Loventre_LMetrics_Structure.v

# 2. SAFE, Complexity, Noise + Class layers
$COQC Loventre_Structural_Sensitivity.v
$COQC Loventre_Complexity_Noise_Stability.v
$COQC Loventre_Class_Noise_Alignment.v
$COQC Loventre_Class_Noise_Separation.v

echo "[B] Complexity/Noise/Class chain OK"

# 3. JSON V32 bridge COMPILATION ORDER
echo "[C] Witness/Bridge/V32"

$COQC Loventre_v32_JSON_Types.v
$COQC Loventre_v32_JSON_Loader.v
$COQC Loventre_v32_JSON_To_LMetrics.v

# 4. Witness loader and link
$COQC Loventre_Witness_Loader.v

echo "=== LOVENTRE V32 — BUILD OK ==="

