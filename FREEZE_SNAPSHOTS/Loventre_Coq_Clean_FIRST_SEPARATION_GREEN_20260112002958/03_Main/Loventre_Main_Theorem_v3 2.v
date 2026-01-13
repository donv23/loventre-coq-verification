(** * Loventre Main Theorem v3 (Full)
    Versione "full" del Main Theorem v3 che estende il Bridge.

    Non ridefiniamo il Main_Theorem_v3_Prop del Bridge.
    Invece costruiamo una proposizione più ricca che combina:

      - il Main Theorem v3 del Bridge (Loventre_Main_Theorem_v3_Prop),
      - il mini teorema P_vs_NPbh Loventre v3:
          * esistenza di un NP_like-black-hole non P_like_accessible,
          * non inclusione della classe NP_bh_Lov in Pacc_Lov.
 *)

From Loventre_Main Require Import
  Loventre_Main_Theorem_v3_Bridge
  Loventre_Mini_Theorem_P_vs_NPbh_Loventre_v3.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

(** ------------------------------------------------------------------ *)
(** 1. Proposizione "full" del Main Theorem v3                        *)
(** ------------------------------------------------------------------ *)

(** Proposizione compatta che raccoglie tre pezzi:

    1. Loventre_Main_Theorem_v3_Prop
       (definita nel Bridge, derivata dal Seed v3).

    2. Loventre_P_vs_NPbh_Loventre_v3_exists_Prop
       = esistenza di un LMetrics in In_NP_bh_Lov ma non in In_Pacc_Lov.

    3. Loventre_P_vs_NPbh_Loventre_v3_nonsubset_Prop
       = la classe In_NP_bh_Lov non è contenuta in In_Pacc_Lov.
 *)

Definition Loventre_Main_Theorem_v3_Full_Prop : Prop :=
  Loventre_Main_Theorem_v3_Prop /\
  Loventre_P_vs_NPbh_Loventre_v3_exists_Prop /\
  Loventre_P_vs_NPbh_Loventre_v3_nonsubset_Prop.

(** ------------------------------------------------------------------ *)
(** 2. Teorema "full" dal Core Program + SAFE                         *)
(** ------------------------------------------------------------------ *)

(** Interpretazione (tutta interna al modello Loventre):

    Assumendo:
      - un programma di policy core (Loventre_Policy_Core_Program),
      - una specifica SAFE (policy_SAFE_implies_green_global),

    otteniamo congiuntamente:

      (i)  il Main Theorem v3 del Bridge (separazione globale P/Pacc/NP_bh
           + SAFE, in forma narrativa);

      (ii) il mini teorema P_vs_NPbh Loventre v3:
             - esistenza di un witness NP_like-black-hole non P_like_accessible,
             - non inclusione della classe NP_bh_Lov nella classe Pacc_Lov.

    Nulla di questo è una dimostrazione di P≠NP classico:
    viviamo sempre nel modello Loventre sul tipo astratto LMetrics.
 *)

Theorem Loventre_Main_Theorem_v3_Full_from_core_and_SAFE :
  Loventre_LMetrics_Policy_Specs.Loventre_Policy_Core_Program ->
  Loventre_LMetrics_Policy_SAFE_Spec.policy_SAFE_implies_green_global ->
  Loventre_Main_Theorem_v3_Full_Prop.
Proof.
  intros Hcore Hsafe.
  unfold Loventre_Main_Theorem_v3_Full_Prop.
  split.
  - (* Parte 1: Main Theorem v3 del Bridge *)
    apply Loventre_Main_Theorem_v3_from_core_and_SAFE; assumption.
  - (* Parte 2+3: mini teorema P_vs_NPbh Loventre v3 *)
    split.
    + apply Loventre_P_vs_NPbh_Loventre_v3_exists.
    + apply Loventre_P_vs_NPbh_Loventre_v3_nonsubset.
Qed.

(** ------------------------------------------------------------------ *)
(** 3. Lemmi di "decompressione" dal Full Main Theorem v3             *)
(** ------------------------------------------------------------------ *)

(** Dal Full Main Theorem v3 possiamo recuperare
    direttamente il Main Theorem v3 del Bridge. *)
Lemma Loventre_Main_Theorem_v3_implies_Bridge :
  Loventre_Main_Theorem_v3_Full_Prop ->
  Loventre_Main_Theorem_v3_Prop.
Proof.
  intro H.
  unfold Loventre_Main_Theorem_v3_Full_Prop in H.
  destruct H as [Hbridge _].
  exact Hbridge.
Qed.

(** Se il Full Main Theorem v3 è vero, allora vale subito
    la parte "esistenza NP_like-black-hole non P_like_accessible". *)
Lemma Loventre_Main_Theorem_v3_implies_NPbh_not_Pacc :
  Loventre_Main_Theorem_v3_Full_Prop ->
  Loventre_P_vs_NPbh_Loventre_v3_exists_Prop.
Proof.
  intro H.
  unfold Loventre_Main_Theorem_v3_Full_Prop in H.
  destruct H as [_ [Hexists _]].
  exact Hexists.
Qed.

(** Se il Full Main Theorem v3 è vero, allora vale subito
    anche la non inclusione NP_bh_Lov ⊄ Pacc_Lov. *)
Lemma Loventre_Main_Theorem_v3_implies_NPbh_nonsubset :
  Loventre_Main_Theorem_v3_Full_Prop ->
  Loventre_P_vs_NPbh_Loventre_v3_nonsubset_Prop.
Proof.
  intro H.
  unfold Loventre_Main_Theorem_v3_Full_Prop in H.
  destruct H as [_ [_ Hnonsub]].
  exact Hnonsub.
Qed.

