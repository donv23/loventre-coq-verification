(* ========================================================== *)
(*  LOVENTRE ENGINE v7 — Witness Index                        *)
(*  Congrega tutti i witness Coq auto-generati.               *)
(*  CANVAS 8 — GENNAIO 2026                                   *)
(* ========================================================== *)

From Stdlib Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

From Coq_IO.LMetrics_v7 Require Import
  LMetrics_v7_Prelude
  LMetrics_v7_types
  witness_json_m_v7_3sat_DIMACS_01
  witness_json_m_v7_3sat_DIMACS_02
  witness_json_m_v7_3sat_DIMACS_03
  witness_json_m_v7_3sat_DIMACS_04
  witness_json_m_v7_3sat_DIMACS_05
  witness_json_m_v7_3sat_DIMACS_06
  witness_json_m_v7_3sat_DIMACS_07
  witness_json_m_v7_3sat_DIMACS_08
  witness_json_m_v7_3sat_DIMACS_09
  witness_json_m_v7_3sat_DIMACS_10
  witness_json_m_v7_3sat_DIMACS_11.

(* ========================================================== *)
(* Lista completa dei witness                                 *)
(* ========================================================== *)

Definition all_v7_witnesses : list LMetricsV7 :=
 [
   witness_m_v7_3sat_DIMACS_01 ;
   witness_m_v7_3sat_DIMACS_02 ;
   witness_m_v7_3sat_DIMACS_03 ;
   witness_m_v7_3sat_DIMACS_04 ;
   witness_m_v7_3sat_DIMACS_05 ;
   witness_m_v7_3sat_DIMACS_06 ;
   witness_m_v7_3sat_DIMACS_07 ;
   witness_m_v7_3sat_DIMACS_08 ;
   witness_m_v7_3sat_DIMACS_09 ;
   witness_m_v7_3sat_DIMACS_10 ;
   witness_m_v7_3sat_DIMACS_11
 ].

Definition v7_count : nat :=
  length all_v7_witnesses.

Lemma v7_has_11 : v7_count = 11.
Proof. reflexivity. Qed.

(* ========================================================== *)
(* FINE                                                        *)
(* ========================================================== *)

