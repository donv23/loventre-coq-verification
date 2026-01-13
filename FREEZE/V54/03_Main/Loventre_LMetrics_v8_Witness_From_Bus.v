(**
  ---------------------------------------------------------
  Loventre_LMetrics_v8_Witness_From_Bus.v
  Preleva i witness dal bus V7 e li esporta come V8
  Congelamento: Gennaio 2026
  ---------------------------------------------------------
*)

From Stdlib Require Import Reals String Bool.
Open Scope R_scope.

(* Import Bus seeds *)
From Loventre_Advanced
     Require Import Loventre_Metrics_Bus.

(* Import package che definisce:
     bus_seed11
     bus_TSPcrit28
     bus_2SAT_easy
     bus_2SAT_crit
 *)
From Loventre_Advanced.Geometry
     Require Import Loventre_LMetrics_v7_Witness_Package.
Import Loventre_Metrics_Bus.

(*
  ---------------------------------------------------------
  Witness V8 (sono semplicemente alias del bus)
  ---------------------------------------------------------
*)

Definition m_seed11_v8 : LMetrics := bus_seed11.
Definition m_TSPcrit28_v8 : LMetrics := bus_TSPcrit28.
Definition m_2SAT_easy_v8 : LMetrics := bus_2SAT_easy.
Definition m_2SAT_crit_v8 : LMetrics := bus_2SAT_crit.

(*
  ---------------------------------------------------------
  Lemma di coerenza minima
  ---------------------------------------------------------
*)
Lemma v8_witness_exist :
  exists a b c d : LMetrics,
    a = m_seed11_v8 /\
    b = m_TSPcrit28_v8 /\
    c = m_2SAT_easy_v8 /\
    d = m_2SAT_crit_v8.
Proof.
  repeat eexists; repeat split; reflexivity.
Qed.

