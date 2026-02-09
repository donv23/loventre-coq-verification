(**
  Loventre_Noise_Regimes_Exclusivity.v

  Exploratory Layer — Noise Regimes
  Minimal exclusivity lemmas (sanity checks)

  No semantics, no dynamics, no assumptions.
*)

Require Import Loventre_Noise_Regimes.

(**
  Distinct noise regimes are not equal.
  Fully qualified names are used.
*)

Lemma inert_not_critical :
  Loventre_Noise_Regimes.Inert_Noise <>
  Loventre_Noise_Regimes.Critical_Noise.
Proof.
  discriminate.
Qed.

Lemma inert_not_horizon_opening :
  Loventre_Noise_Regimes.Inert_Noise <>
  Loventre_Noise_Regimes.Horizon_Opening_Noise.
Proof.
  discriminate.
Qed.

Lemma critical_not_horizon_opening :
  Loventre_Noise_Regimes.Critical_Noise <>
  Loventre_Noise_Regimes.Horizon_Opening_Noise.
Proof.
  discriminate.
Qed.

