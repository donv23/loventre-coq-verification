(*
  Loventre_Mini_Theorem_V980.v
  Versione: V980 — Mini Teorema Interno
  Obiettivo:
    - formalizzare l'esistenza di almeno un witness m
      tale che:
         NP_blackhole(m)
         ~P_like(m)
         ~P_accessible(m)
    nel modello Loventre
  Stato: CANON — nessun Admitted
*)

From Coq Require Import Reals Lia.

From Loventre_Core Require Import Loventre_Prelude.
From Loventre_Core Require Import Loventre_LMetrics_Core.

From Loventre_Advanced Require Import Loventre_LMetrics_JSON_Witness.
From Loventre_Advanced Require Import Loventre_3SATcrit_NoAdmit_V920.
From Loventre_Advanced Require Import Loventre_3SATcrit_Stability_V950.
From Loventre_Advanced Require Import Loventre_Class_Model.
From Loventre_Advanced Require Import Loventre_Class_Dynamics_Bridge_V850.

Open Scope R_scope.

Module Loventre_Mini_Theorem_V980.

  Definition witness := m_3SATcrit.

  (** Proprietà fondamentali già dimostrate nei moduli precedenti *)
  Lemma witness_is_NPbh :
    is_NP_blackhole witness.
  Proof.
    apply threeSATcrit_is_NP_blackhole.
  Qed.

  Lemma witness_not_Plike :
    ~ is_P_like witness.
  Proof.
    apply threeSATcrit_not_P_like.
  Qed.

  Lemma witness_not_Pacc :
    ~ is_P_accessible witness.
  Proof.
    apply threeSATcrit_not_P_accessible.
  Qed.

  (**
     MINI TEOREMA:
     Esiste un witness per cui vale
       NP_blackhole
       ∧ non P-like
       ∧ non P-accessible
   *)
  Theorem Loventre_internal_separation_mini :
    exists w,
        is_NP_blackhole w
      /\ ~ is_P_like w
      /\ ~ is_P_accessible w.
  Proof.
    exists witness.
    repeat split.
    - apply witness_is_NPbh.
    - apply witness_not_Plike.
    - apply witness_not_Pacc.
  Qed.

End Loventre_Mini_Theorem_V980.

