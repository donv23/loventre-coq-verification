(* ======================================================= *)
(* LOVENTRE ENGINE v7 — Import aggregator for LMetrics     *)
(* ======================================================= *)

From Stdlib Require Import ZArith.
Local Open Scope Z_scope.

(* Importiamo tipo canonico LMetricsV7 *)
From LMetrics_v7 Require Export LMetrics_v7_types.

(* Importiamo tutti i witness generati *)
From LMetrics_v7 Require Export
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
     witness_json_m_v7_3sat_DIMACS_11
.

(* Lista aggregata dei witness JSON v7 *)
Definition all_m_v7_witnesses : list LMetricsV7 :=
  (
    witness_m_v7_3sat_DIMACS_01 ::
    witness_m_v7_3sat_DIMACS_02 ::
    witness_m_v7_3sat_DIMACS_03 ::
    witness_m_v7_3sat_DIMACS_04 ::
    witness_m_v7_3sat_DIMACS_05 ::
    witness_m_v7_3sat_DIMACS_06 ::
    witness_m_v7_3sat_DIMACS_07 ::
    witness_m_v7_3sat_DIMACS_08 ::
    witness_m_v7_3sat_DIMACS_09 ::
    witness_m_v7_3sat_DIMACS_10 ::
    witness_m_v7_3sat_DIMACS_11 ::
    nil
  ).

(* Fine del file *)

