(* ******************************************************************* *)
(*  Loventre_LMetrics_Instances.v                                      *)
(*  Catalogo delle istanze LMetrics canoniche                          *)
(* ******************************************************************* *)

From Coq Require Import Reals.

From Loventre_Geometry Require Import Loventre_Metrics_Bus.
From Loventre_Geometry Require Import Loventre_LMetrics_Witness_CLI.

Module MB  := Loventre_Metrics_Bus.
Module CLI := Loventre_LMetrics_Witness_CLI.

Definition LMetrics := MB.LMetrics.

(* Witness CLI *)
Definition witness_cli : LMetrics := CLI.witness_cli.

(* Altri witness verranno aggiunti in seguito                      *)

Lemma Loventre_LMetrics_Instances_dummy : True.
Proof. exact I. Qed.

