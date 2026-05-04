(** * Loventre_Accessible_Status_Bridge
    Bridge: candidato P_like_accessible + stack v2

    Scopo:
      - Collegare in un unico enunciato tre pezzi:
          1) esistenza di almeno una metrica P_like_accessible
             (exists_P_like_accessible_target);
          2) esistenza di un witness NP_like-black-hole NON SAFE
             (Loventre_Theorem_v2_Witness_Bridge_Statement);
          3) separazione di complessità tra i profili
             P_like_complexity_profile e NP_like_crit_complexity_profile
             (Loventre_Complexity_Separation_Statement).

      - Mostrare che, sotto il contratto Loventre
          (Loventre_Policy_Core_Program + SAFE ⇒ GREEN)
        e assumendo che il candidato astratto m_P_like_accessible_candidate
        soddisfi la proprietà m_P_like_accessible_candidate_prop,
        possiamo ottenere simultaneamente questi tre fatti.

    Questo file NON tenta di dimostrare che il candidato sia P_like_accessible:
    tale obiettivo rimane nel lemma m_seed_grid_is_P_like_accessible
    in Loventre_LMetrics_Accessible_Target.v.
 *)

From Loventre_Geometry Require Import
  Loventre_LMetrics_Accessible_Target
  Loventre_LMetrics_Policy_SAFE_Spec
  Loventre_LMetrics_Complexity_Profiles.

From Loventre_Main Require Import
  Loventre_LMetrics_Policy_Specs
  Loventre_Theorem_v2_Witness_Bridge
  Loventre_Mini_Theorem_Stack.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Enunciato "status accessibile" *)

Definition Loventre_Accessible_Status_Prop : Prop :=
  exists_P_like_accessible_target
  /\
  Loventre_Theorem_v2_Witness_Bridge_Statement
  /\
  Loventre_Complexity_Separation_Statement.

(** ** Teorema: dal contratto + candidato accessibile allo status completo

    Ipotesi:
      - Loventre_Policy_Core_Program
      - policy_SAFE_implies_green_global
      - m_P_like_accessible_candidate_prop
          (cioè is_P_like_accessible m_P_like_accessible_candidate)

    Conclusione:
      - Loventre_Accessible_Status_Prop

    Uso:
      - exists_P_like_accessible_from_candidate
      - Loventre_Theorem_v2_Witness_Bridge_from_contract
      - Loventre_Mini_Theorem_Stack_complexity_separation
 *)

Theorem Loventre_Accessible_Status_from_contract_and_candidate :
  Loventre_Policy_Core_Program ->
  policy_SAFE_implies_green_global ->
  m_P_like_accessible_candidate_prop ->
  Loventre_Accessible_Status_Prop.
Proof.
  intros Hcore Hsafe Hacc.
  unfold Loventre_Accessible_Status_Prop.
  split.
  - (* esistenza P_like_accessible dal candidato *)
    unfold m_P_like_accessible_candidate_prop in Hacc.
    apply exists_P_like_accessible_from_candidate.
    exact Hacc.
  - split.
    + (* witness NP_like-black-hole NON SAFE dallo stack v2 *)
      apply Loventre_Theorem_v2_Witness_Bridge_from_contract; assumption.
    + (* separazione di complessità dal Mini_Theorem_Stack *)
      apply Loventre_Mini_Theorem_Stack_complexity_separation; assumption.
Qed.

