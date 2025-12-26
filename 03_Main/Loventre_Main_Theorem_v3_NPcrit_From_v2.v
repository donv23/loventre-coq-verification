(* ******************************************************************* *)
(* Loventre_Main_Theorem_v3_NPcrit_From_v2.v                           *)
(*                                                                     *)
(* Lemma di estrazione per la parte NP_like-critica del Main v3,      *)
(* basato esclusivamente sullo statement di Witness Bridge v2.        *)
(*                                                                     *)
(* In Loventre_Theorem_v2_Witness_Bridge.v è definito:                *)
(*                                                                     *)
(*   Module Ex := Loventre_LMetrics_Existence_Summary.                *)
(*                                                                     *)
(*   Definition Loventre_Theorem_v2_Witness_Bridge_Statement : Prop :=*)
(*     exists m : LMetrics,                                           *)
(*       Ex.is_NP_like_black_hole m /\                               *)
(*       loventre_global_decision m <> GD_safe.                       *)
(*                                                                     *)
(* Il lemma seguente non introduce logica nuova:                      *)
(*   - prende quello statement;                                       *)
(*   - lo riscrive esplicitamente come esistenza di un m_NP con       *)
(*     le stesse proprietà.                                           *)
(*                                                                     *)
(* In una fase successiva, questo lemma fornirà la parte              *)
(* "NP_like_crit non SAFE" richiesta dal Main Theorem v3,             *)
(* istanziando NP_like_crit_profile con Ex.is_NP_like_black_hole.     *)
(* ******************************************************************* *)

From Coq Require Import Init.Logic.

Require Import Loventre_Geometry.Loventre_LMetrics_Existence_Summary.
Require Import Loventre_Main.Loventre_Theorem_v2_Witness_Bridge.

(* Qui riusiamo esattamente gli stessi identificatori: 
   - LMetrics (tipo delle metriche, definito in Geometry)
   - Ex.is_NP_like_black_hole (predicato NP_like-black-hole)
   - loventre_global_decision, GD_safe (Policy globale)
 *)

Lemma Loventre_witness_bridge_implies_NPcrit_not_safe_from_v2 :
  Loventre_Theorem_v2_Witness_Bridge_Statement ->
  exists (m_NP : LMetrics),
    Ex.is_NP_like_black_hole m_NP /\
    loventre_global_decision m_NP <> GD_safe.
Proof.
  intro H.
  (* Lo statement è già nella forma desiderata: basta rinominarne il testimone. *)
  exact H.
Qed.

(* ******************************************************************* *)
(* Fine di Loventre_Main_Theorem_v3_NPcrit_From_v2.v                   *)
(* ******************************************************************* *)

