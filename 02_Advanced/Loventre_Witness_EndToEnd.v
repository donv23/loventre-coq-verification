(** Loventre_Witness_EndToEnd.v
    Witness CANON end-to-end della pipeline decisionale.
*)

From Stdlib Require Import ZArith.

From Loventre_Core Require Import
  Loventre_Kernel
  Loventre_Foundation_Types.

From Loventre_Advanced Require Import
  Loventre_Risk_Level
  Loventre_Risk_Level_Bridge
  Loventre_Policy_Bridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Loventre_Geometry.

(** ============================================================= *)
(** Witness minimale                                              *)
(** ============================================================= *)

Lemma exists_end_to_end_decision :
  exists (x : M)
         (rl : Risk_Level)
         (rc : RiskClass)
         (d  : GlobalDecision),
    RiskLevel_to_RiskClass rl = rc /\
    RiskClass_to_Decision rc = d.
Proof.
  (* Stato base astratto del kernel *)
  exists base_point.

  (* Scelta dichiarativa del livello di rischio *)
  exists RISK_LOW.

  (* Bridge verso RiskClass *)
  exists (RiskLevel_to_RiskClass RISK_LOW).

  (* Bridge verso decisione *)
  exists (RiskClass_to_Decision
            (RiskLevel_to_RiskClass RISK_LOW)).

  split; reflexivity.
Qed.

