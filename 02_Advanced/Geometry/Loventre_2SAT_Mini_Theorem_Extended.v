(**  ***************************************************************  **)
(**    Loventre Project — Geometry Layer — V88 Mini Theorem Ext     **)
(**    CANON FILE — NO ASSIOMS — NO 03_Main                         **)
(**    Autore: Vincenzo Loventre + ChatGPT                          **)
(**    Stato: V88 — Teorema Esteso su famiglie 2-SAT                **)
(**  ***************************************************************  **)

From Coq Require Import List Bool.Bool.
Import ListNotations.

From Loventre_Core Require Import Loventre_LMetrics.

From Loventre_Advanced.Geometry Require Import
     Loventre_LMetrics_Phase_Predicates
     Loventre_2SAT_Local_Family.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Loventre_2SAT_Mini_Theorem_Extended.

  (** ------------------------------------------------------------ *)
  (** 1. Famiglie di witness reimportate                           *)
  (** ------------------------------------------------------------ *)

  Parameter easy_family : list LMetrics.
  Parameter crit_family : list LMetrics.

  Hypothesis all_easy_are_SAFE :
      forall m, In m easy_family -> SAFE_local m.

  Hypothesis all_crit_are_nonSAFE :
      forall m, In m crit_family -> nonSAFE_local m.

  (** ------------------------------------------------------------ *)
  (** 2. Mini-Teorema Esteso                                       *)
  (** ------------------------------------------------------------ *)
  (** Esiste una famiglia Pacc-safe
      ed esiste una famiglia non-Pacc/non-safe                     *)

  Theorem extended_safe_theorem_2sat :
      (exists ef, forall m, In m ef -> SAFE_local m)
   /\ (exists cf, forall m, In m cf -> nonSAFE_local m).
  Proof.
    split.
    - exists easy_family.
      apply all_easy_are_SAFE.
    - exists crit_family.
      apply all_crit_are_nonSAFE.
  Qed.

End Loventre_2SAT_Mini_Theorem_Extended.

