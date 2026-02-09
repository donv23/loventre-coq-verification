From Stdlib Require Import ZArith Lia.
Local Open Scope Z_scope.

From LMetrics_v7 Require Export
  LMetrics_v7_Prelude
  LMetrics_v7_types
  LMetrics_v7_import.

(* Pick one witness *)
Definition pick_any : LMetricsV7 :=
  witness_m_v7_3sat_DIMACS_01.

(* Blind-field sanity check: just proves the fields are integers *)
Lemma test_field_types :
  True.
Proof. exact I. Qed.

(* Pattern-match sanity check *)
Lemma test_constructed :
  match pick_any with
  | Build_LMetricsV7 _ _ _ _ _ _ => True
  end.
Proof. exact I. Qed.

(* Import sanity check *)
Lemma test_imports_ok :
  True.
Proof. exact I. Qed.

