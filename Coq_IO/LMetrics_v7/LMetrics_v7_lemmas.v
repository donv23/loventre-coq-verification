(* ======================================================= *)
(* LOVENTRE ENGINE v7 — Lemmi                             *)
(* ROADMAP 3.1.x                                          *)
(* ======================================================= *)

From Stdlib Require Import ZArith Lia.
Local Open Scope Z_scope.

From LMetrics_v7 Require Import
     LMetrics_v7_types
     LMetrics_v7_import.

(* ------------------------------------------------------- *)
(* Lemma 3.1.1 : Tutti i DIMACS hanno meta_label = 0       *)
(* ------------------------------------------------------- *)

Lemma all_dimacs_meta_label_are_zero :
  (meta_label witness_m_v7_3sat_DIMACS_01 = 0)%Z /\
  (meta_label witness_m_v7_3sat_DIMACS_02 = 0)%Z /\
  (meta_label witness_m_v7_3sat_DIMACS_03 = 0)%Z /\
  (meta_label witness_m_v7_3sat_DIMACS_04 = 0)%Z /\
  (meta_label witness_m_v7_3sat_DIMACS_05 = 0)%Z /\
  (meta_label witness_m_v7_3sat_DIMACS_06 = 0)%Z /\
  (meta_label witness_m_v7_3sat_DIMACS_07 = 0)%Z /\
  (meta_label witness_m_v7_3sat_DIMACS_08 = 0)%Z /\
  (meta_label witness_m_v7_3sat_DIMACS_09 = 0)%Z /\
  (meta_label witness_m_v7_3sat_DIMACS_10 = 0)%Z /\
  (meta_label witness_m_v7_3sat_DIMACS_11 = 0)%Z.
Proof. repeat split; simpl; lia. Qed.

(* ------------------------------------------------------- *)
(* Lemma 3.1.2 : Tutti i DIMACS sono baseline-safe         *)
(* (nel modello Coq: meta_label = 0 -> baseline)           *)
(* ------------------------------------------------------- *)

Definition is_baseline (m : LMetricsV7) : Prop :=
  (meta_label m = 0)%Z.

Lemma all_dimacs_are_baseline_safe :
  is_baseline witness_m_v7_3sat_DIMACS_01 /\
  is_baseline witness_m_v7_3sat_DIMACS_02 /\
  is_baseline witness_m_v7_3sat_DIMACS_03 /\
  is_baseline witness_m_v7_3sat_DIMACS_04 /\
  is_baseline witness_m_v7_3sat_DIMACS_05 /\
  is_baseline witness_m_v7_3sat_DIMACS_06 /\
  is_baseline witness_m_v7_3sat_DIMACS_07 /\
  is_baseline witness_m_v7_3sat_DIMACS_08 /\
  is_baseline witness_m_v7_3sat_DIMACS_09 /\
  is_baseline witness_m_v7_3sat_DIMACS_10 /\
  is_baseline witness_m_v7_3sat_DIMACS_11.
Proof.
  unfold is_baseline.
  apply all_dimacs_meta_label_are_zero.
Qed.

(* ------------------------------------------------------- *)
(* ROADMAP STATUS                                          *)
(* ------------------------------------------------------- *)

(* 3.1.1 COMPLETED *)
(* 3.1.2 COMPLETED PENDING VERDE *)

