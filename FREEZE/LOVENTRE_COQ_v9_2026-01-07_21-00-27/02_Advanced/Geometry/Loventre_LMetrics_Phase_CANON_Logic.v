(* ------------------------------------------------------------
   Loventre_LMetrics_Phase_CANON_Logic.v
   CANON logic covering SAFE + base predicates
   ------------------------------------------------------------ *)

From Stdlib Require Import Reals Bool String.
Open Scope R_scope.

From Loventre_Advanced.Geometry Require Import
     Loventre_LMetrics_Structure
     Loventre_LMetrics_Phase_CANON
     Loventre_LMetrics_Phase_CANON_Index
     Loventre_LMetrics_Phase_CANON_Coherence.

From Loventre_Main Require Import
     Loventre_LMetrics_v9_SAFE.   (* 🔥 questo porta dentro is_SAFE *)

Set Implicit Arguments.
Unset Strict Implicit.

(* ------------------------------------------------------------
   Logic wrappers
   ------------------------------------------------------------ *)

Definition CANON_phase_logic (m : LMetrics) : Prop :=
  is_SAFE m \/ ~ is_SAFE m.

Lemma CANON_phase_logic_total :
  forall m, CANON_phase_logic m.
Proof.
  intros m. unfold CANON_phase_logic.
  destruct (classic (is_SAFE m)); auto.
Qed.

(* Fine Logic *)

