(** Loventre_Main_Theorem_V61.v
    V61 — Consolidated Existence Layer
    Racchiude la struttura V60 in un enunciato principale,
    pronto per essere importato senza i dettagli dei witness.

    Questo file NON sostituisce il V60 — lo re-esprime con un
    focus “da paper”.
 *)

From Stdlib Require Import Bool.

From Loventre_Main Require Import
  Loventre_Main_Prelude
  Loventre_Main_Witness
  Loventre_Main_Witness_2SAT
  Loventre_Main_Predicates
  Loventre_Main_Classes
  Loventre_Main_Theorem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================
         TEOREMA CANONICO V61
    ============================ *)

Theorem loventre_canonical_three_class_v61 :
  exists mP mA mB,
    In_P_like mP /\
    In_P_accessible_like mA /\
    In_NP_blackhole_like mB.
Proof.
  exists m_seed_minimal, m_seed_middle, m_seed_critico.
  apply loventre_internal_separation_v57.
Qed.

(** ============================
       COROLLARIO IN FORMA BREVE
    ============================ *)

Corollary loventre_has_nontrivial_structure_v61 :
  ~ (forall m, In_P_like m) /\
  ~ (forall m, In_P_accessible_like m).
Proof.
  split.
  - eapply existence_of_blackhole_breaks_uniformity;
      [ unfold In_P_like, SAFE; simpl; reflexivity
      | unfold In_NP_blackhole_like, BlackHole; simpl; reflexivity ].
  - eapply existence_of_blackhole_breaks_accessibility;
      unfold In_NP_blackhole_like, BlackHole; simpl; reflexivity.
Qed.

(** ============================
     VISTA “PUBBLICA” DEL MODELLO
    ============================ *)

Definition Loventre_Internal_Truth_V61 : Prop :=
  exists mP mA mB,
    In_P_like mP /\
    In_P_accessible_like mA /\
    In_NP_blackhole_like mB.

Theorem loventre_internal_truth_v61_holds :
  Loventre_Internal_Truth_V61.
Proof.
  unfold Loventre_Internal_Truth_V61.
  apply loventre_canonical_three_class_v61.
Qed.

