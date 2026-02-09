From Stdlib Require Import ZArith Lia.
Local Open Scope Z_scope.

(* ============================== *)
(*  Import minimi necessari       *)
(* ============================== *)

(* Tipo + accessor *)
From LMetrics_v7 Require Import
  LMetrics_v7_types.

(* Witness JSON auto-generati *)
From LMetrics_v7 Require Import
  LMetrics_v7_import.

(* ============================== *)
(*  Sanity tests                  *)
(* ============================== *)

Definition pick_any : LMetricsV7 :=
  witness_m_v7_3sat_DIMACS_01.

Lemma test_field_types :
  kappa_eff pick_any >= 0 /\
  entropy_eff pick_any >= 0 /\
  V0 pick_any >= 0.
Proof.
  repeat split; compute; try lia.
Qed.

Lemma test_constructed :
  match pick_any with
  | Build_LMetricsV7 _ _ _ _ _ _ => True
  end.
Proof. exact I. Qed.

Lemma test_imports_ok :
  True.
Proof. exact I. Qed.

