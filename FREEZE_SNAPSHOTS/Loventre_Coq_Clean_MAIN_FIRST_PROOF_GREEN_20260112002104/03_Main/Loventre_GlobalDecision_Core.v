(** Loventre_GlobalDecision_Core.v
    Core decisionale minimale per il Loventre Metrics Bus v9
 *)

From Stdlib Require Import Bool.Bool.

From Loventre_Advanced Require Import Loventre_Metrics_Bus.
Import Loventre_Metrics_Bus.

Set Implicit Arguments.
Unset Strict Implicit.

Inductive CanonDecision :=
| Dec_Allow
| Dec_Warn
| Dec_Block
| Dec_Investigate
| Dec_Unknown.

Definition loventre_decision (m : LMetrics) : CanonDecision :=
  match loventre_global_decision m with
  | GD_safe        => Dec_Allow
  | GD_borderline  => Dec_Warn
  | GD_critical    => Dec_Block
  | GD_invalid     => Dec_Investigate
  end.

Lemma decision_typed :
  forall m, exists d : CanonDecision, d = loventre_decision m.
Proof.
  intros; repeat eexists; reflexivity.
Qed.

