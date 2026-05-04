(** * Loventre_Main_Stack_SeedGrid
    Variante di stack Main usando il candidato seed_grid

    Scopo:
      - Specializzare Loventre_Main_Stack_from_contract_and_candidate
        al caso in cui l'ipotesi su m_P_like_accessible_candidate_prop
        sia garantita dal lemma-bersaglio m_seed_grid_is_P_like_accessible.

      - Questo file rende esplicito il fatto che, una volta dimostrato
        m_seed_grid_is_P_like_accessible, sarà sufficiente assumere
        solo il contratto Loventre per ottenere l'intero stack Main
        (v2 + v3_mini).
 *)

From Loventre_Geometry Require Import
  Loventre_LMetrics_Accessible_Target
  Loventre_LMetrics_Policy_SAFE_Spec.

From Loventre_Main Require Import
  Loventre_LMetrics_Policy_Specs
  Loventre_Main_Stack_Index.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Prop di stack seed_grid

    Per ora la Prop di stack è semplicemente un alias di
    Loventre_Main_Stack_Prop; manteniamo un nome separato per chiarezza
    semantica ("stack usando seed_grid come candidato P_like_accessible").
 *)

Definition Loventre_Main_Stack_Prop_seedgrid : Prop :=
  Loventre_Main_Stack_Prop.

(** ** Lemma: dal lemma seed_grid otteniamo la proprietà del candidato *)

Lemma m_P_like_accessible_candidate_prop_from_seedgrid :
  m_P_like_accessible_candidate_prop.
Proof.
  unfold m_P_like_accessible_candidate_prop.
  apply m_seed_grid_is_P_like_accessible.
Qed.

(** ** Teorema: dallo stesso contratto + seed_grid allo stack completo *)

Theorem Loventre_Main_Stack_from_contract_and_seedgrid :
  Loventre_Policy_Core_Program ->
  policy_SAFE_implies_green_global ->
  Loventre_Main_Stack_Prop_seedgrid.
Proof.
  intros Hcore Hsafe.
  unfold Loventre_Main_Stack_Prop_seedgrid.
  apply Loventre_Main_Stack_from_contract_and_candidate; try assumption.
  apply m_P_like_accessible_candidate_prop_from_seedgrid.
Qed.

