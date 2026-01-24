(* ******************************************************************* *)
(*  Loventre_LMetrics_Complexity_Profiles.v                           *)
(* ******************************************************************* *)

From Coq Require Import Reals.
From Loventre_Geometry Require Import Loventre_Metrics_Bus.

Module MB := Loventre_Metrics_Bus.

Definition LMetrics := MB.LMetrics.

(* --------------------------------------------------------------- *)
(* RISK CLASS                                                     *)
(* SAFE = classe 0 ; BLACK-HOLE = classe 1                        *)
(* Uso diretto del flag booleano from Metrics_Bus                *)
(* --------------------------------------------------------------- *)
Definition risk_class (m : LMetrics) : nat :=
  if m.(MB.horizon_flag) then 1%nat else 0%nat.

(* --------------------------------------------------------------- *)
(* COMPLEXITY SCORE                                               *)
(* --------------------------------------------------------------- *)
Definition complexity_score (m : LMetrics) : nat :=
  risk_class m.

(* --------------------------------------------------------------- *)
(* LEMMA                                                          *)
(* --------------------------------------------------------------- *)
Lemma risk_class_sound :
  forall m, risk_class m = 0%nat \/ risk_class m = 1%nat.
Proof.
  intro m.
  unfold risk_class.
  destruct (m.(MB.horizon_flag)); simpl; auto.
Qed.

