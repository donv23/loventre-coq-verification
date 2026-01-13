(**  ***************************************************************  **)
(**     Loventre Project — MAIN LAYER — V90.2 Minor Theorem         **)
(**     CANON FILE — NO ASSIOMS — FIRST MAIN-LEVEL INFERENCE        **)
(**     Autore: Vincenzo Loventre + ChatGPT                         **)
(**     Stato: V90 — Main produce un lemma proprio                  **) 
(**  ***************************************************************  **)

From Loventre_Core Require Import Loventre_LMetrics.

(** Import del ponte avvenuto nel passo precedente *)
From Loventre_Main Require Import Loventre_Main_2SAT_Inject.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Loventre_Main_2SAT_Minor_Theorem.

  (** ------------------------------------------------------------ *)
  (** 1. alias locali per leggibilità                              *)
  (** ------------------------------------------------------------ *)

  Definition SAFE := Loventre_Main_2SAT_Inject.SAFE_Lov.
  Definition NotSAFE := Loventre_Main_2SAT_Inject.NotSAFE_Lov.

  Definition easy_family :=
    Loventre_Main_2SAT_Inject.Loventre_2SAT_SAFE_Class.easy_family.

  Definition crit_family :=
    Loventre_Main_2SAT_Inject.Loventre_2SAT_SAFE_Class.crit_family.

  (** ------------------------------------------------------------ *)
  (** 2. Lemma Main: nessun membro easy è nonSAFE                  *)
  (** ------------------------------------------------------------ *)

  Theorem no_easy_member_is_nonSAFE :
      forall m, In m easy_family -> ~ NotSAFE m.
  Proof.
    intros m Hin Hcontra.
    unfold NotSAFE in Hcontra.
    destruct Loventre_Main_2SAT_Inject.class_split_2sat_main_shadow as [Hsafe _].
    specialize (Hsafe m Hin).
    unfold SAFE, Loventre_Main_2SAT_Inject.SAFE_Lov in Hsafe.
    rewrite Hsafe in Hcontra.
    discriminate.
  Qed.

  (** ------------------------------------------------------------ *)
  (** 3. duale: nessun crit member è SAFE                          *)
  (** ------------------------------------------------------------ *)

  Theorem no_crit_member_is_SAFE :
      forall m, In m crit_family -> ~ SAFE m.
  Proof.
    intros m Hin Hcontra.
    unfold SAFE in Hcontra.
    destruct Loventre_Main_2SAT_Inject.class_split_2sat_main_shadow as [_ Hns].
    specialize (Hns m Hin).
    unfold NotSAFE, Loventre_Main_2SAT_Inject.NotSAFE_Lov in Hns.
    rewrite Hns in Hcontra.
    discriminate.
  Qed.

  (** ------------------------------------------------------------ *)
  (** Questo file è il primo in 03_Main che deduce qualcosa        *)
  (**   senza re-esportare semplicemente Geometry/Class            **)
  (** È ancora riflessivo, ma è una deduzione Main                 **)
  (** ------------------------------------------------------------ *)

End Loventre_Main_2SAT_Minor_Theorem.

