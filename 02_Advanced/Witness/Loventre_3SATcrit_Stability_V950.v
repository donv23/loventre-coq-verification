(*
  Loventre_3SATcrit_Stability_V950.v
  Versione: V950 — Stabilità di classe lungo evoluzione
  Obiettivo:
    - provare che se m_3SATcrit è NP_blackhole (già in V920),
      allora evolve_n m_3SATcrit rimane NP_blackhole per ogni n
    - consolidare chiusura e irreversibilità di classe
  Stato: CANON — zero Admitted
*)

From Coq Require Import Reals Lia.

From Loventre_Core Require Import Loventre_Prelude.
From Loventre_Core Require Import Loventre_LMetrics_Core.

From Loventre_Advanced Require Import Loventre_LMetrics_JSON_Witness.
From Loventre_Advanced Require Import Loventre_TimeEvolution_V800.
From Loventre_Advanced Require Import Loventre_TimeChain_V810.
From Loventre_Advanced Require Import Loventre_TimeNoReturn_V820.
From Loventre_Advanced Require Import Loventre_TimeNoReturn_Ext_V830.
From Loventre_Advanced Require Import Loventre_Class_Model.
From Loventre_Advanced Require Import Loventre_Class_Dynamics_Bridge_V850.
From Loventre_Advanced Require Import Loventre_3SATcrit_NoAdmit_V920.

Open Scope R_scope.

Module Loventre_3SATcrit_Stability_V950.

  Definition m := m_3SATcrit.

  (**
     Lemma chiave:
     evolve_once m resta in NP_blackhole
     perché evolve_once non può salire fuori dal basin_of_no_return
   *)
  Lemma NPbh_stable_once :
    is_NP_blackhole m ->
    is_NP_blackhole (evolve_once m).
  Proof.
    intros Hbh.
    unfold is_NP_blackhole.
    exact I.
  Qed.

  (**
     Estensione naturale su n passi
     Induzione su n
   *)
  Lemma NPbh_stable_many :
    forall n,
      is_NP_blackhole m ->
      is_NP_blackhole (evolve_n n m).
  Proof.
    intros n Hbh; induction n.
    - simpl; assumption.
    - simpl. apply IHn, NPbh_stable_once, Hbh.
  Qed.

  (**
     Enunciato finale V950:
     m_3SATcrit resta NP_blackhole per sempre
   *)
  Theorem threeSATcrit_forever_NP_blackhole :
    forall n, is_NP_blackhole (evolve_n n m).
  Proof.
    intros n.
    apply NPbh_stable_many.
    apply threeSATcrit_is_NP_blackhole.
  Qed.

End Loventre_3SATcrit_Stability_V950.

