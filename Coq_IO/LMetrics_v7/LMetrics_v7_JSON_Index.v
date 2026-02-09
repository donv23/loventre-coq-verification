(* LMetrics_v7_JSON_Index.v
   Import minimale test per i witness JSON v7
*)

From Stdlib Require Import ZArith List.
Import ListNotations.
Local Open Scope Z_scope.

(* Modulistica LMetrics *)
From LMetrics_v7 Require Import
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

(* Lista minima di witness a scopo di test *)

Definition all_m_v7_witnesses : list LMetricsV7 :=
  [
    witness_m_v7_3sat_DIMACS_01;
    witness_m_v7_3sat_DIMACS_02;
    witness_m_v7_3sat_DIMACS_03;
    witness_m_v7_3sat_DIMACS_04;
    witness_m_v7_3sat_DIMACS_05;
    witness_m_v7_3sat_DIMACS_06;
    witness_m_v7_3sat_DIMACS_07;
    witness_m_v7_3sat_DIMACS_08;
    witness_m_v7_3sat_DIMACS_09;
    witness_m_v7_3sat_DIMACS_10;
    witness_m_v7_3sat_DIMACS_11
  ].

