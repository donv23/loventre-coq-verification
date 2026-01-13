From Stdlib Require Import Reals.
From Loventre_Geometry Require Import
  Loventre_LMetrics_JSON_Witness
  Loventre_LMetrics_Existence_Summary.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

(** Questo file definisce predicati "di fase" derivati sui campi di [LMetrics]
    e li collega ai predicati astratti [is_P_like] e [is_NP_like_black_hole]
    già definiti in [Loventre_LMetrics_Existence_Summary]. *)

(** 1. Predicati di base sui campi di LMetrics *)

Definition is_low_risk (m : LMetrics) : Prop :=
  risk_class m = risk_LOW.

Definition is_black_hole (m : LMetrics) : Prop :=
  horizon_flag m = true.

Definition is_non_black_hole (m : LMetrics) : Prop :=
  horizon_flag m = false.

Definition has_P_like_label (m : LMetrics) : Prop :=
  meta_label m = meta_P_like_like.

Definition has_NP_like_black_hole_label (m : LMetrics) : Prop :=
  meta_label m = meta_NP_like_black_hole.

(** 1.1. Predicato per la fase P-like "accessibile/borderline green"

    NOTA: questo predicato non fa riferimento a un witness specifico.
    È una descrizione astratta:
    - low risk
    - non black-hole
    - decisione GD_borderline
    - colore GC_green.
 *)

Definition is_P_like_accessible (m : LMetrics) : Prop :=
  is_low_risk m /\
  is_non_black_hole m /\
  loventre_global_decision m = GD_borderline /\
  loventre_global_color m = GC_green.

(** 2. Collegamenti generali fra fasi astratte e predicati di base *)

Lemma is_P_like_implies_low_risk_non_black_hole :
  forall m : LMetrics,
    is_P_like m -> is_low_risk m /\ is_non_black_hole m.
Proof.
  intros m H.
  unfold is_P_like in H.
  unfold is_low_risk, is_non_black_hole.
  destruct H as (_Hmeta & Hrisk & Hhorizon).
  split; assumption.
Qed.

Lemma is_P_like_implies_full_profile :
  forall m : LMetrics,
    is_P_like m ->
    has_P_like_label m /\ is_low_risk m /\ is_non_black_hole m.
Proof.
  intros m H.
  unfold is_P_like in H.
  unfold has_P_like_label, is_low_risk, is_non_black_hole.
  destruct H as (Hmeta & Hrisk & Hhorizon).
  repeat split; assumption.
Qed.

Lemma is_NP_like_black_hole_implies_full_profile :
  forall m : LMetrics,
    is_NP_like_black_hole m ->
    has_NP_like_black_hole_label m /\
    risk_class m = risk_NP_like_black_hole /\
    is_black_hole m.
Proof.
  intros m H.
  unfold is_NP_like_black_hole in H.
  unfold has_NP_like_black_hole_label, is_black_hole.
  destruct H as (Hmeta & Hrisk & Hhorizon).
  repeat split; assumption.
Qed.

(** 3. Specializzazione ai witness concreti *)

Lemma m_seed11_is_low_risk_non_black_hole :
  is_low_risk m_seed11_cli_demo /\ is_non_black_hole m_seed11_cli_demo.
Proof.
  apply is_P_like_implies_low_risk_non_black_hole.
  apply m_seed11_soddisfa_is_P_like.
Qed.

Lemma m_seed11_has_P_like_full_profile :
  has_P_like_label m_seed11_cli_demo /\
  is_low_risk m_seed11_cli_demo /\
  is_non_black_hole m_seed11_cli_demo.
Proof.
  apply is_P_like_implies_full_profile.
  apply m_seed11_soddisfa_is_P_like.
Qed.

Lemma m_TSPcrit28_is_black_hole_full_profile :
  has_NP_like_black_hole_label m_TSPcrit28_cli_demo /\
  risk_class m_TSPcrit28_cli_demo = risk_NP_like_black_hole /\
  is_black_hole m_TSPcrit28_cli_demo.
Proof.
  apply is_NP_like_black_hole_implies_full_profile.
  apply m_TSPcrit28_soddisfa_is_NP_like_black_hole.
Qed.

Lemma m_SATcrit16_is_black_hole_full_profile :
  has_NP_like_black_hole_label m_SATcrit16_cli_demo /\
  risk_class m_SATcrit16_cli_demo = risk_NP_like_black_hole /\
  is_black_hole m_SATcrit16_cli_demo.
Proof.
  apply is_NP_like_black_hole_implies_full_profile.
  apply m_SATcrit16_soddisfa_is_NP_like_black_hole.
Qed.

