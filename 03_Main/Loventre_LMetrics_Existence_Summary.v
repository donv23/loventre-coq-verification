(* *********************************************************************** *)
(*  Loventre_LMetrics_Existence_Summary.v                                  *)
(* *********************************************************************** *)

From Coq Require Import Reals.

From Loventre_Geometry Require Import Loventre_Metrics_Bus.
From Loventre_Geometry Require Import Loventre_LMetrics_Instances.

Module MB := Loventre_Metrics_Bus.
Definition LMetrics := MB.LMetrics.

(* Esistenza triviale: esiste una metrica del bus. Non facciamo confronti. *)
Theorem exists_some_LMetrics :
  exists m : LMetrics, True.
Proof.
  (* prendiamo il witness standard lato CLI *)
  exists witness_cli.
  trivial.
Qed.

(* Modulo exportato *)
Module Export Loventre_LMetrics_Existence_Export.
  Theorem existence_summary :
    exists m : LMetrics, True.
  Proof.
    apply exists_some_LMetrics.
  Qed.
End Loventre_LMetrics_Existence_Export.

