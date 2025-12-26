(* ******************************************************************* *)
(*  Loventre_Namespace_Core.v                                         *)
(*  Dichiarazione globale del namespace Loventre                      *)
(* ******************************************************************* *)

From Stdlib Require Import List.
From Stdlib Require Import Nat.

(* Import the physical path where the bus actually lives. *)
Require Import Loventre_Metrics_Bus.

(* bind the bus to the logical namespace Loventre.LMetrics *)
Module Loventre.LMetrics.
  Export Loventre_Metrics_Bus.
End Loventre.LMetrics.

Lemma loventre_namespace_core_ok : True.
Proof. exact I. Qed.

