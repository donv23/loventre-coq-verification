(** Loventre_Policy_Bridge.v
    Bridge CANON tra RiskClass e decisione globale.
    Nessuna logica classica, nessuna totalità inversa.
*)

From Stdlib Require Import ZArith.

From Loventre_Core Require Import
  Loventre_Kernel
  Loventre_Foundation_Types.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** ============================================================= *)
(** Decisioni globali astratte                                    *)
(** ============================================================= *)

Inductive GlobalDecision : Set :=
| DECISION_GREEN
| DECISION_YELLOW
| DECISION_RED.

(** ============================================================= *)
(** Bridge dichiarativo                                           *)
(** ============================================================= *)

Definition RiskClass_to_Decision (rc : RiskClass) : GlobalDecision :=
  match rc with
  | risk_LOW                 => DECISION_GREEN
  | risk_MID                 => DECISION_YELLOW
  | risk_NP_like_black_hole  => DECISION_RED
  end.

(** ============================================================= *)
(** Lemma di totalità (banale, CANON)                             *)
(** ============================================================= *)

Lemma RiskClass_to_Decision_total :
  forall rc : RiskClass,
    exists d : GlobalDecision,
      RiskClass_to_Decision rc = d.
Proof.
  intro rc; exists (RiskClass_to_Decision rc); reflexivity.
Qed.

(** NOTA CANON:
    - Nessuna proprietà semantica su GREEN/YELLOW/RED
    - Nessuna implicazione decisione -> rischio
*)

