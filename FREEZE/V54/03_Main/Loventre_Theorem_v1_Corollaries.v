(* Loventre_Theorem_v1_Corollaries.v
   Corollari "ready-to-use" di LOVENTRE_THEOREM_V1.

   Scopo: offrire enunciati più semplici estratti da
   Loventre_Theorem_v1_Statement, senza introdurre nuove ipotesi.
*)

From Stdlib Require Import Reals.

From Loventre_Geometry Require Import
  Loventre_LMetrics_JSON_Witness
  Loventre_LMetrics_Existence_Summary
  Loventre_LMetrics_Phase_Predicates
  Loventre_LMetrics_Policy_SAFE_Spec.

From Loventre_Main Require Import
  Loventre_LMetrics_Policy_Specs
  Loventre_LMetrics_Separation_Program
  Loventre_Theorem_v1.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

Module JSONW    := Loventre_LMetrics_JSON_Witness.
Module Ex       := Loventre_LMetrics_Existence_Summary.
Module Phase    := Loventre_LMetrics_Phase_Predicates.
Module SafeSpec := Loventre_LMetrics_Policy_SAFE_Spec.
Module Core     := Loventre_LMetrics_Policy_Specs.
Module SepProg  := Loventre_LMetrics_Separation_Program.

Import JSONW Phase.

(** ------------------------------------------------------------------------ *)
(** 1. Notazioni ausiliarie                                                  *)
(** ------------------------------------------------------------------------ *)

Definition Loventre_P_world_exists_from_contract
           (Hcore : Core.Loventre_Policy_Core_Program)
           (Hsafe : SafeSpec.policy_SAFE_implies_green_global) : Prop :=
  exists mP : LMetrics, is_P_like mP.

Definition Loventre_P_accessible_world_exists_from_contract
           (Hcore : Core.Loventre_Policy_Core_Program)
           (Hsafe : SafeSpec.policy_SAFE_implies_green_global) : Prop :=
  exists mPa : LMetrics, is_P_like_accessible mPa.

Definition Loventre_NP_world_exists_from_contract
           (Hcore : Core.Loventre_Policy_Core_Program)
           (Hsafe : SafeSpec.policy_SAFE_implies_green_global) : Prop :=
  exists mN : LMetrics, is_NP_like_black_hole mN.

Definition Loventre_NP_world_non_safe_witness_from_contract
           (Hcore : Core.Loventre_Policy_Core_Program)
           (Hsafe : SafeSpec.policy_SAFE_implies_green_global) : Prop :=
  exists m : LMetrics,
    is_NP_like_black_hole m /\
    loventre_global_decision m <> GD_safe.

(** ------------------------------------------------------------------------ *)
(** 2. Corollari estratti da Loventre_Theorem_v1_Statement                   *)
(** ------------------------------------------------------------------------ *)

Lemma Loventre_P_world_exists_from_contract_lemma :
  forall (Hcore : Core.Loventre_Policy_Core_Program)
         (Hsafe : SafeSpec.policy_SAFE_implies_green_global),
    Loventre_P_world_exists_from_contract Hcore Hsafe.
Proof.
  intros Hcore Hsafe.
  unfold Loventre_P_world_exists_from_contract.
  (* Usiamo LOVENTRE_THEOREM_V1 *)
  unfold Loventre_Theorem_v1_Statement.
  pose proof (Loventre_Theorem_v1_from_contract Hcore Hsafe) as Hth.
  destruct Hth as [Hsep _]. (* separazione LMetrics + witness NP_non_SAFE *)
  (* spacchettiamo la parte SepProg.Loventre_LMetrics_Separation_Statement *)
  unfold SepProg.Loventre_LMetrics_Separation_Statement in Hsep.
  destruct Hsep as [Htriple _].
  unfold SepProg.Loventre_P_Paccessible_NP_like_triple_prop in Htriple.
  destruct Htriple as [HexP [_ _]].
  exact HexP.
Qed.

Lemma Loventre_P_accessible_world_exists_from_contract_lemma :
  forall (Hcore : Core.Loventre_Policy_Core_Program)
         (Hsafe : SafeSpec.policy_SAFE_implies_green_global),
    Loventre_P_accessible_world_exists_from_contract Hcore Hsafe.
Proof.
  intros Hcore Hsafe.
  unfold Loventre_P_accessible_world_exists_from_contract.
  unfold Loventre_Theorem_v1_Statement.
  pose proof (Loventre_Theorem_v1_from_contract Hcore Hsafe) as Hth.
  destruct Hth as [Hsep _].
  unfold SepProg.Loventre_LMetrics_Separation_Statement in Hsep.
  destruct Hsep as [Htriple _].
  unfold SepProg.Loventre_P_Paccessible_NP_like_triple_prop in Htriple.
  destruct Htriple as [_ [HexPa _]].
  exact HexPa.
Qed.

Lemma Loventre_NP_world_exists_from_contract_lemma :
  forall (Hcore : Core.Loventre_Policy_Core_Program)
         (Hsafe : SafeSpec.policy_SAFE_implies_green_global),
    Loventre_NP_world_exists_from_contract Hcore Hsafe.
Proof.
  intros Hcore Hsafe.
  unfold Loventre_NP_world_exists_from_contract.
  unfold Loventre_Theorem_v1_Statement.
  pose proof (Loventre_Theorem_v1_from_contract Hcore Hsafe) as Hth.
  destruct Hth as [Hsep _].
  unfold SepProg.Loventre_LMetrics_Separation_Statement in Hsep.
  destruct Hsep as [Htriple _].
  unfold SepProg.Loventre_P_Paccessible_NP_like_triple_prop in Htriple.
  destruct Htriple as [_ [_ HexN]].
  exact HexN.
Qed.

Lemma Loventre_NP_world_non_safe_witness_from_contract_lemma :
  forall (Hcore : Core.Loventre_Policy_Core_Program)
         (Hsafe : SafeSpec.policy_SAFE_implies_green_global),
    Loventre_NP_world_non_safe_witness_from_contract Hcore Hsafe.
Proof.
  intros Hcore Hsafe.
  unfold Loventre_NP_world_non_safe_witness_from_contract.
  unfold Loventre_Theorem_v1_Statement.
  pose proof (Loventre_Theorem_v1_from_contract Hcore Hsafe) as Hth.
  destruct Hth as [_ HexistNP].
  exact HexistNP.
Qed.

