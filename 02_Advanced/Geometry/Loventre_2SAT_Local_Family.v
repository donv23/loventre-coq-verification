(**  ***************************************************************  **)
(**      Loventre Project — Geometry Layer — V87 Local Family       **)
(**      CANON FILE — NO ASSIOMS — NO 03_Main                        **)
(**      Autore: Vincenzo Loventre + ChatGPT                         **)
(**      Stato: V87 — Famiglie easy/crit, SAFE/nonSAFE               **)
(**  ***************************************************************  **)

From Coq Require Import List Bool.Bool.
Import ListNotations.

From Loventre_Core Require Import Loventre_LMetrics.

From Loventre_Advanced.Geometry Require Import
     Loventre_LMetrics_Phase_Predicates
     Loventre_2SAT_Pacc_Class_Bridge
     Loventre_2SAT_SAFE_Bridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Loventre_2SAT_Local_Family.

  (** ------------------------------------------------------------ *)
  (** 1. Famiglie di witness (easy e crit)                          *)
  (** ------------------------------------------------------------ *)

  Parameter easy_family : list LMetrics.
  Parameter crit_family : list LMetrics.

  (** ------------------------------------------------------------ *)
  (** 2. Condizioni di base già dimostrate singolarmente            *)
  (** ------------------------------------------------------------ *)

  Hypothesis all_easy_are_Pacc :
      forall m, In m easy_family -> is_pacc_2sat m = true.

  Hypothesis all_crit_are_not_Pacc :
      forall m, In m crit_family -> is_pacc_2sat m = false.

  (** ------------------------------------------------------------ *)
  (** 3. SAFE vs NON SAFE per famiglie                              *)
  (** ------------------------------------------------------------ *)

  Definition SAFE_local (m : LMetrics) : Prop :=
    is_pacc_2sat m = true.

  Definition nonSAFE_local (m : LMetrics) : Prop :=
    is_pacc_2sat m = false.

  (** ------------------------------------------------------------ *)
  (** 4. Lemmi familiari                                            *)
  (** ------------------------------------------------------------ *)

  Lemma all_easy_are_SAFE_local :
      forall m, In m easy_family -> SAFE_local m.
  Proof.
    intros m Hin.
    unfold SAFE_local.
    apply all_easy_are_Pacc.
    exact Hin.
  Qed.

  Lemma all_crit_are_nonSAFE_local :
      forall m, In m crit_family -> nonSAFE_local m.
  Proof.
    intros m Hin.
    unfold nonSAFE_local.
    apply all_crit_are_not_Pacc.
    exact Hin.
  Qed.

  (** ------------------------------------------------------------ *)
  (** 5. Teorema locale familiare                                  *)
  (** ------------------------------------------------------------ *)
  (** Tutti gli easy ⇒ SAFE
      Tutti i crit  ⇒ nonSAFE                                         *)

  Theorem family_safe_split_2sat :
      (forall m, In m easy_family -> SAFE_local m)
   /\ (forall m, In m crit_family -> nonSAFE_local m).
  Proof.
    split.
    - apply all_easy_are_SAFE_local.
    - apply all_crit_are_nonSAFE_local.
  Qed.

End Loventre_2SAT_Local_Family.

