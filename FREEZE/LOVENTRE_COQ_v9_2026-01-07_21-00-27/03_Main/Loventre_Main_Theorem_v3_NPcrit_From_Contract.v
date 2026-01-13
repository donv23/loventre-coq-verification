(* ******************************************************************* *)
(* Loventre_Main_Theorem_v3_NPcrit_From_Contract.v                     *)
(*                                                                     *)
(* Gamba NP del Main Theorem v3:                                       *)
(*   dal contratto (Core Program + SAFE ⇒ GREEN) e dai risultati v2    *)
(*   (Witness Bridge) otteniamo l'esistenza di un witness               *)
(*   NP_like-black-hole NON SAFE.                                      *)
(*                                                                     *)
(* Questo file non introduce logica nuova:                             *)
(*   - usa lo statement di bridge v2;                                  *)
(*   - usa il lemma di estrazione                                     *)
(*       Loventre_witness_bridge_implies_NPcrit_not_safe_from_v2;      *)
(*   - conclude con un enunciato esistenziale "contratto → ∃ m_NP ...". *)
(* ******************************************************************* *)

From Stdlib Require Import Init.Logic.

Require Import Loventre_Main.Loventre_Theorem_v2_Witness_Bridge.
Require Import Loventre_Main.Loventre_Main_Theorem_v3_NPcrit_From_v2.

(* Richiamo per contesto (già definito in Loventre_Theorem_v2_Witness_Bridge):
   - Loventre_Policy_Core_Program : Prop
   - policy_SAFE_implies_green_global : Prop
   - Loventre_Theorem_v2_Witness_Bridge_Statement : Prop
   - Loventre_Theorem_v2_Witness_Bridge_from_contract :
       Loventre_Policy_Core_Program ->
       policy_SAFE_implies_green_global ->
       Loventre_Theorem_v2_Witness_Bridge_Statement
   - Ex.is_NP_like_black_hole : _ -> Prop
   - loventre_global_decision : _ -> _
   - GD_safe : _
 *)

Theorem Loventre_v3_NPcrit_from_contract :
  Loventre_Policy_Core_Program ->
  policy_SAFE_implies_green_global ->
  exists m_NP,
    Ex.is_NP_like_black_hole m_NP /\
    loventre_global_decision m_NP <> GD_safe.
Proof.
  intros Hcore Hsafe.
  (* 1. Dal contratto otteniamo lo statement di Witness Bridge v2. *)
  pose proof (Loventre_Theorem_v2_Witness_Bridge_from_contract Hcore Hsafe)
    as Hbridge.
  (* 2. Usiamo il lemma di estrazione per riscriverlo nella forma
        esistenziale desiderata. *)
  apply Loventre_witness_bridge_implies_NPcrit_not_safe_from_v2 in Hbridge.
  exact Hbridge.
Qed.

(* ******************************************************************* *)
(* Fine di Loventre_Main_Theorem_v3_NPcrit_From_Contract.v             *)
(* ******************************************************************* *)

