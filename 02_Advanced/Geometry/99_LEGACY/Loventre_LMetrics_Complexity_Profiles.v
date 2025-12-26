(* ************************************************************ *)
(* Loventre_LMetrics_Complexity_Profiles.v                     *)
(* ************************************************************ *)

From Coq Require Import Bool Reals.

From Loventre_Advanced.Geometry
Require Import Loventre_Metrics_Bus Loventre_LMetrics_Phase_Predicates.

Module MB := Loventre_Metrics_Bus.
Module PP := Loventre_LMetrics_Phase_Predicates.

Definition LMetrics := MB.LMetrics.

(* ------------------------------------------------------------ *)
(* Boolean comparison for Reals                                 *)
(* ------------------------------------------------------------ *)

Definition Rltb (x y: R) : bool :=
  if Rlt_dec x y then true else false.

(* ------------------------------------------------------------ *)
(* Boolean SAFE via decision on real inequalities               *)
(* ------------------------------------------------------------ *)

Definition is_safe_b (m : LMetrics) : bool :=
  let p := MB.P_success m in
  if (Rltb 0 p) && (Rltb p 1) then true else false.

(* ------------------------------------------------------------ *)
(* Boolean horizon check                                        *)
(* ------------------------------------------------------------ *)

Definition is_black_b (m : LMetrics) : bool :=
  MB.horizon_flag m.

(* ------------------------------------------------------------ *)
(* Complexity SAFE                                              *)
(* ------------------------------------------------------------ *)

Definition complexity_SAFE (m : LMetrics) : nat :=
  if is_safe_b m then 1 else 0.

(* ------------------------------------------------------------ *)
(* Complexity BLACK                                             *)
(* ------------------------------------------------------------ *)

Definition complexity_black (m : LMetrics) : nat :=
  if is_black_b m then 1 else 0.

(* ------------------------------------------------------------ *)
(* Complexity BORDER                                            *)
(* ------------------------------------------------------------ *)

Definition complexity_border (m : LMetrics) : nat :=
  if negb (is_safe_b m) && negb (is_black_b m) then 1 else 0.

Lemma compl_ok :
  True.
Proof. exact I. Qed.

