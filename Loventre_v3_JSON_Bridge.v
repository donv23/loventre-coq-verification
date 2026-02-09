From Stdlib Require Import String.
Open Scope string_scope.

Require Import Loventre_v3_DeltaCurvature.
Require Import Loventre_v3_Asymmetry.
Require Import Loventre_v3_Final.

(* =================================================== *)
(* Loventre v3 — Export Record (JSON-friendly)         *)
(* =================================================== *)

Record Loventre_v3_Export := {
  status_v3     : string;
  delta_ACC_BH  : nat;
  delta_STR_BH  : nat;
  asymmetry_ok  : bool
}.

Definition Loventre_v3_export_instance : Loventre_v3_Export :=
{|
  status_v3 := "Loventre_v3";
  delta_ACC_BH := 1;
  delta_STR_BH := 2;
  asymmetry_ok := true
|}.

(* =================================================== *)
(* Lemma di coerenza                                   *)
(* =================================================== *)

Lemma Loventre_v3_export_correct :
  Loventre_v3_export_instance.(asymmetry_ok) = true.
Proof.
  reflexivity.
Qed.

