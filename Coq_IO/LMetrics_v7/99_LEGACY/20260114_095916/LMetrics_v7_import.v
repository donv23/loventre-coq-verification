(* LOVENTRE ENGINE v7 — Import aggregator for LMetrics witnesses *)

From Stdlib Require Import ZArith.
Local Open Scope Z_scope.

(* Esportiamo il tipo canonico *)
From LMetrics_v7 Require Export LMetrics_v7_types.

(* Esportiamo tutti i witness generati *)
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

