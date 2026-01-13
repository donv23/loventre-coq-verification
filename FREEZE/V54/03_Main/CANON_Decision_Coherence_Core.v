(* ------------------------------------------------------------
   CANON_Decision_Coherence_Core.v
   Coerenza tra CANON Phase e Decision Core
   ------------------------------------------------------------ *)

From Stdlib Require Import Reals Bool String.
Open Scope R_scope.

From Loventre_Advanced.Geometry Require Import
     Loventre_LMetrics_Structure
     Loventre_LMetrics_Phase_CANON
     Loventre_LMetrics_Phase_CANON_Index
     Loventre_LMetrics_Phase_CANON_Logic
     Loventre_LMetrics_Phase_CANON_Coherence.

From Loventre_Main Require Import
     CANON_Decision_Core.

Set Implicit Arguments.
Unset Strict Implicit.

(* ------------------------------------------------------------
   Coerenza fondamentale
   ------------------------------------------------------------ *)

Theorem CANON_decision_coherent :
  forall m : LMetrics,
    CANON_phase_logic m -> CANON_decision_defined m.
Proof.
  intros m H.
  unfold CANON_decision_defined.
  destruct H; auto.
Qed.

(* Accesso al totale della logica *)
Lemma CANON_decision_total :
  forall m, CANON_decision_defined m.
Proof.
  intro m.
  apply CANON_decision_coherent.
  apply CANON_phase_logic_total.
Qed.

(* Fine *)

