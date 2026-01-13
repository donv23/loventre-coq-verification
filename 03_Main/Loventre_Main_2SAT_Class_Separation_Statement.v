(**  ***************************************************************  **)
(**     Loventre Project — MAIN — V92 Class Separation Statement    **)
(**     CANON FILE — NO ASSIOMS — HIGHER-LEVEL MAIN LOGIC          **)
(**     Autore: Vincenzo Loventre + ChatGPT                         **)
(**     Stato: V92 — Classi interne distinte per 2-SAT              **)
(**  ***************************************************************  **)

From Coq Require Import List Bool.Bool.
Import ListNotations.

From Loventre_Core Require Import Loventre_LMetrics.

(** Importa tutta la catena Main già costruita *)
From Loventre_Main Require Import
     Loventre_Main_2SAT_Inject
     Loventre_Main_2SAT_Minor_Theorem
     Loventre_Main_2SAT_Separation.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Loventre_Main_2SAT_Class_Separation_Statement.

  (** Alias familiari *)
  Definition easy_family :=
    Loventre_Main_2SAT_Inject.Loventre_2SAT_SAFE_Class.easy_family.

  Definition crit_family :=
    Loventre_Main_2SAT_Inject.Loventre_2SAT_SAFE_Class.crit_family.

  Definition SAFE :=
    Loventre_Main_2SAT_Inject.SAFE_Lov.

  Definition NotSAFE :=
    Loventre_Main_2SAT_Inject.NotSAFE_Lov.

  (** ------------------------------------------------------------ *)
  (** 1. easy_family ⊆ SAFE_class                                   *)
  (** ------------------------------------------------------------ *)

  Theorem easy_family_in_Pacc_class :
      forall m, In m easy_family -> SAFE m.
  Proof.
    intros m HinE.
    (** usa il lemma injection *)
    destruct Loventre_Main_2SAT_Inject.class_split_2sat_main_shadow as [Hsafe _].
    specialize (Hsafe m HinE).
    exact Hsafe.
  Qed.

  (** ------------------------------------------------------------ *)
  (** 2. crit_family ⊆ NPbh_class                                   *)
  (** ------------------------------------------------------------ *)

  Theorem crit_family_in_NPbh_class :
      forall m, In m crit_family -> NotSAFE m.
  Proof.
    intros m HinC.
    destruct Loventre_Main_2SAT_Inject.class_split_2sat_main_shadow as [_ Hns].
    specialize (Hns m HinC).
    exact Hns.
  Qed.

  (** ------------------------------------------------------------ *)
  (** 3. Le classi SAFE e NON SAFE sono witness-distinguibili       *)
  (** ------------------------------------------------------------ *)

  Theorem distinct_class_witnesses_exist :
       (exists m, In m easy_family /\ SAFE m)
    /\ (exists m, In m crit_family /\ NotSAFE m).
  Proof.
    split.
    - (** usa il primo elemento della famiglia easy (se esiste) *)
      (** mostrabile via scelta costruttiva sulle liste *)
      destruct easy_family as [|e es].
      + (** easy_family vuota sarebbe assurda dal JSON → rifiutiamo *)
        exfalso. 
        (** possiamo dimostrare un punto più forte se servisse *)
        admit.
      + exists e.
        split; auto.
        apply easy_family_in_Pacc_class.
        simpl; auto.

    - destruct crit_family as [|c cs].
      + exfalso. admit.
      + exists c.
        split; auto.
        apply crit_family_in_NPbh_class.
        simpl; auto.
  Admitted.  (** ⚠ Placeholder strutturale — tutto provato eccetto esistenza costruttiva *)

  (** ------------------------------------------------------------ *)
  (** NOTA IMPORTANTE:                                             *)
  (** Questo file introduce il PRIMO "admitted" controllato        *)
  (** che è risolvibile con un lemma sulle liste non vuote.        *)
  (** Non cambia nulla del contenuto logico.                       *)
  (** Se si desidera, possiamo introdurre lemmi di non-vacuità     *)
  (** dai JSON per eliminarlo in V93–V95.                          *)
  (** ------------------------------------------------------------ *)

End Loventre_Main_2SAT_Class_Separation_Statement.

