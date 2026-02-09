#!/usr/bin/env bash
set -e

echo "=== LOVENTRE V32 — FULL DEPENDENCY BUILD START ==="

# Root safety
ROOT_DIR="$(cd "$(dirname "$0")" && pwd)"
cd "$ROOT_DIR"

# -------------------------------------------------------------------
# (0) Build v3 canon first (needed for Loventre_v3_JSON_Bridge etc.)
# -------------------------------------------------------------------
echo "[0] Build CANON v3 (coqc_all_v3.sh)"
bash coqc_all_v3.sh

# -------------------------------------------------------------------
# (A) SAFE + LMetrics chain (order-sensitive)
# -------------------------------------------------------------------
echo "[A] SAFE + LMetrics chain"
coqc Loventre_SAFE_Predicate.v
coqc Loventre_Global_Invariant_Stub.v

coqc Loventre_LMetrics_Structure.v
coqc Loventre_LMetrics_Robustness.v
coqc Loventre_LMetrics_Robustness_Lemmas.v
coqc Loventre_LMetrics_Perturbation.v
coqc Loventre_LMetrics_Dynamic_Perturbation.v
coqc Loventre_LMetrics_Dynamic_Perturbation_Identity.v

# -------------------------------------------------------------------
# (B) Complexity/Noise/Class chain (THIS FIXES YOUR CURRENT ERROR)
# -------------------------------------------------------------------
echo "[B] Complexity/Noise/Class chain"
coqc Loventre_Complexity_Noise_Stability.v
coqc Loventre_Complexity_Noise_Classes.v

coqc Loventre_Noise_Regimes.v
coqc Loventre_Noise_Regimes_Order.v
coqc Loventre_Noise_Regimes_Exclusivity.v

coqc Loventre_Class_Noise_Interface.v
coqc Loventre_Class_Noise_Alignment.v
coqc Loventre_Class_Noise_Separation.v
coqc Loventre_Class_Membership.v

# -------------------------------------------------------------------
# (C) Witness loader + SAFE bridge + V32 witness-from-JSON
# -------------------------------------------------------------------
echo "[C] Witness/Bridge/V32"
coqc Loventre_Witness_Loader.v
coqc Loventre_SAFE_Bridge.v
coqc Loventre_V32_Witness_From_JSON.v

echo "=== LOVENTRE V32 — BUILD OK (GREEN) ==="

