(** Loventre_Mini_Theorem_EndToEnd.v
    Mini-teorema CANON:
    esistenza di una decisione globale ottenibile
    tramite la pipeline Loventre end-to-end.

    Nessuna computazione.
    Nessuna logica classica.
    Nessuna inversione di bridge.
*)

From Stdlib Require Import ZArith.

From Loventre_Core Require Import
  Loventre_Kernel
  Loventre_Foundation_Types.

From Loventre_Advanced Require Import
  Loventre_Risk_Level
  Loventre_Risk_Level_Bridge
  Loventre_Policy_Bridge
  Loventre_Witness_EndToEnd.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Loventre_Geometry.

(** ============================================================= *)
(** Mini-teorema End-to-End                                      *)
(** ============================================================= *)

Theorem Loventre_Mini_Theorem_EndToEnd :
  exists (x  : M)
         (rl : Risk_Level)
         (rc : RiskClass)
         (d  : GlobalDecision),
    RiskLevel_to_RiskClass rl = rc /\
    RiskClass_to_Decision rc = d.
Proof.
  exact exists_end_to_end_decision.
Qed.

