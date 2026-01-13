(**  ***************************************************************  **)
(**       Loventre Project — MAIN LAYER — V90 2-SAT Injection       **)
(**       CANON FILE — NO NEW AXIOMS — NO THEOREMS ADDED YET        **)
(**       Autore: Vincenzo Loventre + ChatGPT                       **)
(**       Stato: V90 — Import formale in 03_Main                     **)
(**  ***************************************************************  **)

From Loventre_Core Require Import Loventre_LMetrics.

(** Importiamo SOLO il risultato di classe V89 *)
From Loventre_Advanced Require Import Loventre_2SAT_SAFE_Class.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Loventre_Main_2SAT_Inject.

  (** ------------------------------------------------------------ *)
  (** 1. Rexport “classi” provenienti dal layer Geometry/Class      *)
  (** ------------------------------------------------------------ *)

  Definition In_Pacc_Lov := Loventre_2SAT_SAFE_Class.In_Pacc_Loventre.
  Definition In_NPbh_Lov := Loventre_2SAT_SAFE_Class.In_NPbh_Loventre.
  Definition SAFE_Lov    := Loventre_2SAT_SAFE_Class.SAFE_Loventre.
  Definition NotSAFE_Lov := Loventre_2SAT_SAFE_Class.NotSAFE_Loventre.

  (** ------------------------------------------------------------ *)
  (** 2. Primo riferimento ai risultati familiari                  *)
  (** ------------------------------------------------------------ *)

  Theorem class_split_2sat_main_shadow :
        (forall m, In m Loventre_2SAT_SAFE_Class.easy_family -> SAFE_Lov m)
     /\ (forall m, In m Loventre_2SAT_SAFE_Class.crit_family -> NotSAFE_Lov m).
  Proof.
    apply Loventre_2SAT_SAFE_Class.class_split_2sat.
  Qed.

  (** ------------------------------------------------------------ *)
  (** Nessun altro lemma. Nessuna interpretazione. Nessun salto.   *)
  (** Ora 03_Main sa che:                                          *)
  (**   - esistono due famiglie                                   *)
  (**   - easy family è SAFE                                      *)
  (**   - crit family è NON SAFE                                  *)
  (** esattamente come dimostrato nei livelli inferiori.           *)
  (** ------------------------------------------------------------ *)

End Loventre_Main_2SAT_Inject.

