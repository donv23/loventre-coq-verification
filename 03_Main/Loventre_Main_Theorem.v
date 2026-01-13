(** Loventre_Main_Theorem.v
    V57-08 — Mini-Teorema + Lemmi ponte coerenti
 *)

From Stdlib Require Import Bool.

From Loventre_Main Require Import
  Loventre_Main_Prelude
  Loventre_Main_Witness
  Loventre_Main_Predicates
  Loventre_Main_Classes.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================
        MINI TEOREMA V57-08
    ============================ *)

Theorem loventre_internal_separation_v57 :
  In_P_like m_seed_minimal /\
  In_P_accessible_like m_seed_middle /\
  In_NP_blackhole_like m_seed_critico.
Proof.
  split.
  - unfold In_P_like, SAFE; simpl; reflexivity.
  - split.
    + unfold In_P_accessible_like, SAFE, BlackHole; simpl.
      split; [reflexivity|].
      intro H; discriminate.
    + unfold In_NP_blackhole_like, BlackHole; simpl; reflexivity.
Qed.

(** ============================
      COROLLARIO DI ESISTENZA
    ============================ *)

Corollary loventre_internal_separation_exists_v57 :
  exists m1 m2 m3,
    In_P_like m1 /\
    In_P_accessible_like m2 /\
    In_NP_blackhole_like m3.
Proof.
  exists m_seed_minimal, m_seed_middle, m_seed_critico.
  apply loventre_internal_separation_v57.
Qed.

(** ============================
        LEMMI PONTE V57-08
    ============================ *)

Lemma not_all_P_like_if_blackhole_exists :
  In_NP_blackhole_like m_seed_critico ->
  ~ (In_P_like m_seed_minimal /\
     In_P_like m_seed_middle /\
     In_P_like m_seed_critico).
Proof.
  intros Hbh [Hmin [Hmid Hcrit]].
  unfold In_P_like, SAFE in Hcrit.
  unfold In_NP_blackhole_like, BlackHole in Hbh.
  simpl in *.
  rewrite Hcrit in Hbh.
  discriminate.
Qed.

Lemma existence_of_blackhole_breaks_uniformity :
  In_P_like m_seed_minimal ->
  In_NP_blackhole_like m_seed_critico ->
  ~ (forall m, In_P_like m).
Proof.
  intros Hmin Hbh Hall.
  specialize (Hall m_seed_critico).
  unfold In_P_like, SAFE in Hall.
  unfold In_NP_blackhole_like, BlackHole in Hbh.
  simpl in *.
  rewrite Hall in Hbh.
  discriminate.
Qed.

Lemma existence_of_blackhole_breaks_accessibility :
  In_NP_blackhole_like m_seed_critico ->
  ~ (forall m, In_P_accessible_like m).
Proof.
  intros Hbh Hall.
  specialize (Hall m_seed_critico) as Hacc.
  unfold In_P_accessible_like in Hacc.
  destruct Hacc as [Hsafe _].
  unfold SAFE, In_NP_blackhole_like, BlackHole in *.
  simpl in *.
  rewrite Hsafe in Hbh.
  discriminate.
Qed.

