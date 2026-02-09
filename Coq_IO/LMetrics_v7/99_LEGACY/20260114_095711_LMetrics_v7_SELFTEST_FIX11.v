From Stdlib Require Import ZArith Lia.
Local Open Scope Z_scope.

From LMetrics_v7 Require Export
  LMetrics_v7_Prelude
  LMetrics_v7_types
  LMetrics_v7_import.

(* Pick one witness *)
Definition pick_any : LMetricsV7 :=
  witness_m_v7_3sat_DIMACS_01.

(* All fields must be non-negative *)
Lemma test_field_types :
  kappa_eff pick_any >= 0 /\
  entropy_eff pick_any >= 0 /\
  mass_eff pick_any >= 0 /\
  inertial_idx pick_any >= 0 /\
  risk_index pick_any >= 0 /\
  meta_label pick_any >= 0.
Proof.
  repeat split; compute; try lia.
Qed.

(* Witness must match the record constructor *)
Lemma test_constructed :
  match pick_any with
  | Build_LMetricsV7 _ _ _ _ _ _ => True
  end.
Proof. exact I. Qed.

(* Import sanity check *)
Lemma test_imports_ok :
  True.
Proof. exact I. Qed.

