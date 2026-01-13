(* ******************************************************************* *)
(*  Loventre_LMetrics_Witness_Lemmas.v                                 *)
(* ******************************************************************* *)

From Stdlib Require Import Reals.
From Loventre_Geometry Require Import Loventre_Metrics_Bus.
From Loventre_Geometry Require Import Loventre_LMetrics_Complexity_Profiles.
From Loventre_Geometry Require Import Loventre_LMetrics_Complexity_Witness.

Module MB := Loventre_Metrics_Bus.
Module CP := Loventre_LMetrics_Complexity_Profiles.
Module W  := Loventre_LMetrics_Complexity_Witness.

Definition LMetrics := MB.LMetrics.

(* ------------------------------------------------------------ *)
(* SAFE witness lemma                                           *)
(* ------------------------------------------------------------ *)
Lemma m_safe_is_safe :
  CP.risk_class W.m_safe = 0%nat.
Proof.
  apply W.m_safe_score.
Qed.

(* ------------------------------------------------------------ *)
(* BLACK-HOLE witness lemma                                     *)
(* ------------------------------------------------------------ *)
Lemma m_black_is_black :
  CP.risk_class W.m_black = 1%nat.
Proof.
  apply W.m_black_score.
Qed.


