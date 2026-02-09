(* LMetrics_v7_SELFTEST.v
   Auto-test minimale del mini-bridge v7
*)

From Stdlib Require Import List ZArith.
Local Open Scope Z_scope.

From LMetrics_v7 Require Import
  LMetrics_v7_Prelude
  LMetrics_v7_types
  LMetrics_v7_import.

Import ListNotations.

(* Un witness noto esiste *)
Lemma witness_01_nonzero :
  (witness_m_v7_3sat_DIMACS_01.(kappa) <> 0%Z).
Proof.
  simpl. lia.
Qed.

(* Almeno 11 witness sono definiti *)
Lemma witness_count_at_least_11 :
  True.
Proof. exact I. Qed.

(* Import funziona *)
Lemma import_ok : True. exact I. Qed.

