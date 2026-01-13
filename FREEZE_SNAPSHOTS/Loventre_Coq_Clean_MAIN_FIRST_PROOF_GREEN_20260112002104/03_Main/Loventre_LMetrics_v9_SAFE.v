(** Loventre_LMetrics_v9_SAFE.v
    SAFE logic v9 — uso diretto del Loventre Metrics Bus
 *)

From Stdlib Require Import Bool.Bool Arith Lia Reals.
Open Scope R_scope.

From Loventre_Advanced Require Import Loventre_Metrics_Bus.
Import Loventre_Metrics_Bus.

Set Implicit Arguments.
Unset Strict Implicit.

(** SAFE = (horizon_flag = false) /\ (loventre_global_decision = GD_safe)
    NOTE:
      - horizon_flag : bool
      - loventre_global_decision : GlobalDecision
 *)

Definition loventre_is_safe (m : LMetrics) : bool :=
  if (horizon_flag m)
  then false
  else
    match loventre_global_decision m with
    | GD_safe => true
    | _       => false
    end.

(** Versione logica proposizionale (Prop) *)
Definition loventre_safe_prop (m : LMetrics) : Prop :=
  horizon_flag m = false /\
  loventre_global_decision m = GD_safe.

Lemma safe_soundness :
  forall m, loventre_is_safe m = true -> loventre_safe_prop m.
Proof.
  intros m H.
  unfold loventre_is_safe in H.
  destruct (horizon_flag m) eqn:HF.
  - discriminate H.
  - destruct (loventre_global_decision m) eqn:GD;
      simpl in H; try discriminate; subst.
    split; auto.
Qed.

Lemma safe_completeness :
  forall m, loventre_safe_prop m -> loventre_is_safe m = true.
Proof.
  intros m [HF HG].
  unfold loventre_is_safe.
  rewrite HF, HG. reflexivity.
Qed.

