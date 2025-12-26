(* ============================================================ *)
(*  Loventre_Main_Theorem_v3_Bridge.v                          *)
(*  Dicembre 2025 — Bridge tra teorema principale e versione   *)
(*  standardizzata per test                                    *)
(* ============================================================ *)

From Stdlib Require Import Reals.

From Loventre_Advanced Require Import Loventre_Metrics_Bus.
From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Phase_Predicates
  Loventre_LMetrics_Existence_Summary.

From Loventre_Main Require Import Loventre_Main_Theorem_v3.

Import Loventre_Metrics_Bus.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================================================ *)
(**  Bridge: alias logico tra i due enunciati                   *)
(** ============================================================ *)

Definition Loventre_Main_Theorem_v3_statement : Prop :=
  exists mP mNP : LMetrics,
    is_P_like mP /\ is_NP_like_black_hole mNP.

(** ============================================================ *)
(**  Bridge Theorem — coerente col teorema principale           *)
(** ============================================================ *)

Theorem Loventre_Main_Theorem_v3_Bridge :
  Loventre_Main_Theorem_v3_statement.
Proof.
  unfold Loventre_Main_Theorem_v3_statement.
  destruct Loventre_Main_Theorem_v3_Prop as [mP [mNP [HP HNP]]].
  exists mP, mNP.
  split; assumption.
Qed.

