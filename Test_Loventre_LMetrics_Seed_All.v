(* Test_Loventre_LMetrics_Seed_All.v *)

From Stdlib Require Import Reals.
Require Import Loventre_Metrics_Bus.
Require Import Loventre_LMetrics_JSON_Witness.

Open Scope R_scope.

Lemma test_w1_ok :
  (kappa_eff witness_crit1) = (-6)%R.
Proof. reflexivity. Qed.

Lemma test_w2_ok :
  (entropy_eff witness_crit2) = (-11)%R.
Proof. reflexivity. Qed.

Lemma test_w3_ok :
  (V0 witness_crit3) = (0)%R.
Proof. reflexivity. Qed.

Lemma test_w4_ok :
  (kappa_eff witness_crit4) = (77)%R.
Proof. reflexivity. Qed.

Lemma seeds_ok : True.
Proof. exact I. Qed.

