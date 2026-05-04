(** * Loventre_Main_Theorem_v3_Mini
    Mini Main v3 basato su Accessible_Status_Bridge

    Scopo:
      - Fornire una versione minimale del "Main Theorem v3" che
        non entra nei dettagli delle scelte concrete di m_P, m_Pacc, m_NP,
        ma riassume lo stato "contratto + candidato accessibile" come
        un'unica proposizione Loventre_Main_Prop_v3_mini.

      - Questo file NON sostituisce Loventre_Main_Theorem.v della tab fredda:
        è un wrapper minimale che potrà essere confrontato o integrato
        con l'enunciato completo di Loventre_Main_Prop in seguito.
 *)

From Loventre_Geometry Require Import
  Loventre_LMetrics_Accessible_Target
  Loventre_LMetrics_Policy_SAFE_Spec
  Loventre_LMetrics_Complexity_Profiles.

From Loventre_Main Require Import
  Loventre_LMetrics_Policy_Specs
  Loventre_Theorem_v2_Witness_Bridge
  Loventre_Mini_Theorem_Stack
  Loventre_Accessible_Status_Bridge.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

(** ** Definizione minimale del Main Prop v3

    Qui scegliamo di usare direttamente Loventre_Accessible_Status_Prop
    come "Main Prop v3 minimale":

      - esistenza di almeno una metrica P_like_accessible;
      - esistenza di un witness NP_like-black-hole NON SAFE;
      - separazione di complessità tra profili P_like e NP_like_crit.

    In futuro, Loventre_Main_Prop (nella versione completa) potrà
    raffinare questa proposizione, ma questa definizione è già
    sufficiente per rappresentare l'idea di tre fasi distinte
    (P_like, P_like_accessible, NP_like_critica NON SAFE).
 *)

Definition Loventre_Main_Prop_v3_mini : Prop :=
  Loventre_Accessible_Status_Prop.

(** ** Teorema mini-Main v3 dal contratto + candidato

    Ipotesi:
      - Loventre_Policy_Core_Program
      - policy_SAFE_implies_green_global
      - m_P_like_accessible_candidate_prop

    Conclusione:
      - Loventre_Main_Prop_v3_mini

    Prova:
      - delega a Loventre_Accessible_Status_from_contract_and_candidate.
 *)

Theorem Loventre_Main_Theorem_v3_mini_from_contract :
  Loventre_Policy_Core_Program ->
  policy_SAFE_implies_green_global ->
  m_P_like_accessible_candidate_prop ->
  Loventre_Main_Prop_v3_mini.
Proof.
  intros Hcore Hsafe Hacc.
  unfold Loventre_Main_Prop_v3_mini.
  apply Loventre_Accessible_Status_from_contract_and_candidate; assumption.
Qed.


