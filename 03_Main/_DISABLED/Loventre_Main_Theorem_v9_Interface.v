(*
  ---------------------------------------------------------
  Loventre_Main_Theorem_v9_Interface.v
  Interfaccia V9 — nomenclatura e view astratte
  ---------------------------------------------------------
*)

From Stdlib Require Import Reals Bool String.
Open Scope R_scope.

From Loventre_Advanced Require Import Loventre_Metrics_Bus.
Import Loventre_Metrics_Bus.

From Loventre_Main Require Import
     Loventre_Main_Theorem_v9_Prelude
     Loventre_LMetrics_v9_SAFE
     Loventre_LMetrics_v9_Aliases
     Loventre_LMetrics_v9_Policy
     Loventre_LMetrics_v9_Risk
     Loventre_LMetrics_v9_MetaDecision
     Loventre_LMetrics_v9_OneShot
     Loventre_LMetrics_v9_Witness_Package.

Set Implicit Arguments.
Unset Strict Implicit.

(*
  ---------------------------------------------------------
  Classificazione V9 (nominale)
  Niente prove forti, nessun assioma.
  ---------------------------------------------------------
*)

Inductive Loventre_Class :=
| Class_P_Like
| Class_BH_Like
| Class_Unknown.

(*
  Mappa MetaDecision → classe nominale
  ---------------------------------------------------------
*)

Definition classify_v9 (m : LMetrics) : Loventre_Class :=
  match loventre_decide_v9_oneshot m with
  | Meta_Allow | Meta_Warn => Class_P_Like
  | Meta_Block | Meta_Investigate => Class_BH_Like
  end.

(*
  Predicati nominali
  ---------------------------------------------------------
*)

Definition In_P_Like_Loventre (m : LMetrics) : Prop :=
  classify_v9 m = Class_P_Like.

Definition In_BH_Like_Loventre (m : LMetrics) : Prop :=
  classify_v9 m = Class_BH_Like.

Definition In_Unknown_Loventre (m : LMetrics) : Prop :=
  classify_v9 m = Class_Unknown.

(*
  ---------------------------------------------------------
  Risultato nominale per i due witness V9
  (nessuna pretesa, solo definizioni simboliche)
  ---------------------------------------------------------
*)

Definition seed11_is_Plike : Prop :=
  In_P_Like_Loventre seed11.

Definition sat2crit_is_BHlike : Prop :=
  In_BH_Like_Loventre sat2_crit.

(* Fine Interfaccia V9 *)

