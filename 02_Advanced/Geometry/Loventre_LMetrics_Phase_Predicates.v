(** Loventre_LMetrics_Phase_Predicates.v
    Versione minimale CANONICA senza bus o JSON.
 *)

From Loventre_Core Require Import
  Loventre_Kernel
  Loventre_Foundation_Types.

From Loventre_Advanced Require Import
  Loventre_SAFE_Model
  Loventre_Class_Model.

Import Loventre_Geometry.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Predicato: fase P_like se è in P (contractibile) *)
Definition Phase_P_like (x : M) : Prop :=
  In_P_Lov x.

(** Predicato: fase P_accessible se P + stabilità *)
Definition Phase_P_accessible (x : M) : Prop :=
  In_Pacc_Lov x.

(** Predicato: fase NP_blackhole-like se non contrattibile *)
Definition Phase_NP_blackhole (x : M) : Prop :=
  In_NPbh_Lov x.

(** Esclusione: NPbh implica non P *)
Lemma Phase_NPbh_not_P :
  forall x : M,
    Phase_NP_blackhole x ->
    ~ Phase_P_like x.
Proof.
  intros x HNP HP.
  unfold Phase_NP_blackhole in HNP.
  unfold Phase_P_like in HP.
  eapply In_NPbh_Lov_not_P; eauto.
Qed.

