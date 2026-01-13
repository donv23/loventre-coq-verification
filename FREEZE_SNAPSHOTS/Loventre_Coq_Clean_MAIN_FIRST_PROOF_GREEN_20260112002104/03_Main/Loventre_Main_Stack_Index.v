(** * Loventre_Main_Stack_Index
    Indice compatto dello stack Main (v2 + v3_mini)

    Scopo:
      - Fornire un unico "entrypoint" logico che combina:
          1) il Mini Teorema v2 (Loventre_Mini_Theorem_Stack_Statement);
          2) il Mini Main Theorem v3 (Loventre_Main_Prop_v3_mini).

      - Dal punto di vista concettuale:
          Contratto Loventre
          + candidato P_like_accessible
          ⇒ (stack v2) ∧ (Main v3 minimale).
 *)

From Loventre_Geometry Require Import
  Loventre_LMetrics_Accessible_Target
  Loventre_LMetrics_Policy_SAFE_Spec
  Loventre_LMetrics_Complexity_Profiles.

From Loventre_Main Require Import
  Loventre_LMetrics_Policy_Specs
  Loventre_Mini_Theorem_Stack
  Loventre_Main_Theorem_v3_Mini.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Prop di stack globale *)

Definition Loventre_Main_Stack_Prop : Prop :=
  Loventre_Mini_Theorem_Stack_Statement
  /\
  Loventre_Main_Prop_v3_mini.

(** ** Teorema: dallo stesso contratto a tutto lo stack *)

Theorem Loventre_Main_Stack_from_contract_and_candidate :
  Loventre_Policy_Core_Program ->
  policy_SAFE_implies_green_global ->
  m_P_like_accessible_candidate_prop ->
  Loventre_Main_Stack_Prop.
Proof.
  intros Hcore Hsafe Hacc.
  unfold Loventre_Main_Stack_Prop.
  split.
  - (* Parte v2: Mini_Theorem_Stack *)
    apply Loventre_Mini_Theorem_Stack_from_contract; assumption.
  - (* Parte v3_mini: Main_Prop_v3_mini *)
    apply Loventre_Main_Theorem_v3_mini_from_contract; assumption.
Qed.

