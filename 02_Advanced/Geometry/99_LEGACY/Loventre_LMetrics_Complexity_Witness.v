(* ************************************************************ *)
(* Loventre_LMetrics_Complexity_Witness.v                       *)
(* ************************************************************ *)

From Coq Require Import Reals Bool Arith.
From Loventre_Advanced Require Import Loventre_Metrics_Bus.
From Loventre_Advanced Require Import Loventre_LMetrics_Complexity_Profiles.
From Loventre_Advanced Require Import Loventre_LMetrics_Phase_Predicates.

Module MB := Loventre_Metrics_Bus.
Module PP := Loventre_LMetrics_Phase_Predicates.
Module CP := Loventre_LMetrics_Complexity_Profiles.

Definition LMetrics := MB.LMetrics.

(* ------------------------------------------------------------ *)
(* Complexity signature                                         *)
(* ------------------------------------------------------------ *)

Definition complexity_signature (m : LMetrics) : nat * nat * nat :=
  (CP.complexity_SAFE m,
   CP.complexity_black m,
   CP.complexity_border m).

(* ------------------------------------------------------------ *)
(* Witnesses                                                     *)
(* ------------------------------------------------------------ *)

Definition witness_is_safe (m : LMetrics) : bool :=
  if CP.is_safe_b m then true else false.

Definition witness_is_black (m : LMetrics) : bool :=
  if CP.is_black_b m then true else false.

Definition witness_is_border (m : LMetrics) : bool :=
  if andb (negb (CP.is_safe_b m)) (negb (CP.is_black_b m))
  then true else false.

(* ------------------------------------------------------------ *)
(* Lemma dummy                                                   *)
(* ------------------------------------------------------------ *)

Lemma complexity_witness_ok :
  True.
Proof. exact I. Qed.

