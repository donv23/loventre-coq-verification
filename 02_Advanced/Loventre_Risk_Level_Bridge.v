(** Loventre_Risk_Level_Bridge.v
    Bridge CANON tra:
    - Risk_Level   (dinamica / geometria)
    - RiskClass    (LMetrics / policy)
    Nessuna assunzione di totalità o ordine.
*)

From Stdlib Require Import ZArith.

From Loventre_Core Require Import
  Loventre_Kernel
  Loventre_Foundation_Types.

From Loventre_Advanced Require Import
  Loventre_Risk_Level.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Loventre_Geometry.

(** ============================================================= *)
(** Bridge dichiarativo                                           *)
(** ============================================================= *)

Definition RiskLevel_to_RiskClass (r : Risk_Level) : RiskClass :=
  match r with
  | RISK_LOW    => risk_LOW
  | RISK_MEDIUM => risk_MID
  | RISK_HIGH   => risk_NP_like_black_hole
  end.

(** ============================================================= *)
(** Lemmi di coerenza (puramente strutturali)                     *)
(** ============================================================= *)

Lemma RiskLevel_to_RiskClass_total :
  forall r : Risk_Level,
    exists rc : RiskClass,
      RiskLevel_to_RiskClass r = rc.
Proof.
  intro r; exists (RiskLevel_to_RiskClass r); reflexivity.
Qed.

(** NOTA CANON:
    - Nessun lemma del tipo risk_high -> risk_MID
    - Nessuna inversione (RiskClass -> Risk_Level)
    - Bridge unidirezionale e dichiarativo
*)

