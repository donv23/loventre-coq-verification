(**  ***************************************************************  **)
(**     Loventre Project — MAIN LAYER — V90.3 Separation            **)
(**     CANON FILE — NO ASSIOMS — STRUCTURED MAIN RESULT            **)
(**     Autore: Vincenzo Loventre + ChatGPT                         **)
(**     Stato: V90 — Famiglie 2-SAT sono disgiunte nel Main         **) 
(**  ***************************************************************  **)

From Coq Require Import List Bool.Bool.
Import ListNotations.

From Loventre_Core Require Import Loventre_LMetrics.

(** Importiamo sia l'injection, sia i minor lemma *)
From Loventre_Main Require Import
     Loventre_Main_2SAT_Inject
     Loventre_Main_2SAT_Minor_Theorem.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Loventre_Main_2SAT_Separation.

  (** ------------------------------------------------------------ *)
  (** 1. Liste alias per compattezza                               *)
  (** ------------------------------------------------------------ *)

  Definition easy_family :=
    Loventre_Main_2SAT_Inject.Loventre_2SAT_SAFE_Class.easy_family.

  Definition crit_family :=
    Loventre_Main_2SAT_Inject.Loventre_2SAT_SAFE_Class.crit_family.

  Definition SAFE :=
    Loventre_Main_2SAT_Inject.SAFE_Lov.

  Definition NotSAFE :=
    Loventre_Main_2SAT_Inject.NotSAFE_Lov.

  (** ------------------------------------------------------------ *)
  (** 2. Lemma di incompatibilità                                  *)
  (** ------------------------------------------------------------ *)

  Lemma easy_member_not_crit_member :
      forall m,
        In m easy_family ->
        In m crit_family ->
        False.
  Proof.
    intros m HinE HinC.
    (** SAFE da easy *)
    pose proof (Loventre_Main_2SAT_Minor_Theorem.no_easy_member_is_nonSAFE m HinE) as Hsafe.
    (** NON SAFE da crit *)
    pose proof (Loventre_Main_2SAT_Minor_Theorem.no_crit_member_is_SAFE m HinC) as Hnsafe.
    (** Ora SAFE m /\ ~SAFE m, contraddizione *)
    apply Hnsafe.
    unfold SAFE.
    (** SAFE m è ottenuto usando injection e class split *)
    destruct Loventre_Main_2SAT_Inject.class_split_2sat_main_shadow as [HsafeClass _].
    specialize (HsafeClass m HinE).
    unfold SAFE, Loventre_Main_2SAT_Inject.SAFE_Lov in HsafeClass.
    rewrite HsafeClass.
    exact I.
  Qed.

  (** ------------------------------------------------------------ *)
  (** 3. La famiglia easy e quella crit NON si sovrappongono       *)
  (** ------------------------------------------------------------ *)

  Theorem easy_crit_families_disjoint :
      forall m, In m easy_family -> ~ In m crit_family.
  Proof.
    intros m HinE HinC.
    eapply easy_member_not_crit_member; eauto.
  Qed.

  (** ------------------------------------------------------------ *)
  (** Questo lemma è il primo risultato “strutturale” del Main:    *)
  (**   easy-family e crit-family NON condividono elementi         *)
  (**                                                            **)
  (** È ancora interno al sistema Loventre, senza claim esterni.   *)
  (** Testimone reale + logica pura → separazione interna           *)
  (** ------------------------------------------------------------ *)

End Loventre_Main_2SAT_Separation.

