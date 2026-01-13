(** Loventre_Main_Index.v
    Entry-point CANON del livello Main del modello Loventre.

    Questo file importa esclusivamente:
    - Core
    - Advanced (via indice)
    - e re-esporta TUTTI i moduli Main V9
*)

From Loventre_Core Require Import
  Loventre_Kernel
  Loventre_Foundation_Types
  Loventre_Foundation_Params
  Loventre_Foundation_Entropy.

From Loventre_Advanced Require Import
  Loventre_Advanced_Index.

(** --------------------------------------------------------- *)
(**  Routing dei moduli MAIN V9                              *)
(** --------------------------------------------------------- *)

Require Export Loventre_GlobalDecision_Core.
Require Export CANON_Decision_Core.
Require Export CANON_Decision_Coherence_Core.

Require Export Loventre_LMetrics_v9_SAFE.
Require Export Loventre_LMetrics_v9_Aliases.
Require Export Loventre_LMetrics_v9_Risk.
Require Export Loventre_LMetrics_v9_Policy.
Require Export Loventre_LMetrics_v9_MetaDecision.
Require Export Loventre_LMetrics_v9_OneShot.

(** --------------------------------------------------------- *)
(**  Routing Witness CANON                                   *)
(** --------------------------------------------------------- *)

Require Export Witnesses.CANON.Loventre_Witness_CANON_Index.

(** Fine Main Index V9 *)

