(* ========================================================= *)
(* LOVENTRE ENGINE v7 — LMetrics INDEX (Coq_IO entrypoint)    *)
(* Collega i witness JSON con i bridge v7                    *)
(* ========================================================= *)

From Stdlib Require Import ZArith Bool.
Local Open Scope Z_scope.

(* Import diretti dei moduli interni a Coq_IO *)
Require Import LMetrics_v7_Prelude.
Require Import LMetrics_v7_types.
Require Import LMetrics_v7_import.

(* Import Advanced Bridge unificato dalla radice LMetrics_v7 *)
Require Import LMetrics_v7_BridgeIndex.

(* Alias unico per esporre tutto *)
Module LMetricsV7.
  Export LMetrics_v7_Bridge.
End LMetricsV7.

(* Smoke: almeno un witness esiste *)
Lemma index_has_witness :
  exists m : LMetricsV7.LMetricsV7, True.
Proof.
  exists witness_json_m_v7_3sat_DIMACS_01.
  exact I.
Qed.

