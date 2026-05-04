(*
  Trichotomy_Theorems.v

  Formal results for Chapter 26:
  Non-eludibility of structural trichotomy.
*)

Require Import Loventre_Advanced.Structural_Trichotomy.Trichotomy_Core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ===================================================== *)
(* === Non-eludibility of classification               === *)
(* ===================================================== *)

Theorem no_unclassified_configuration :
  ~ (exists x : Config,
       ~ Stable x /\ ~ Critical x /\ ~ Isolating x).
Proof.
  intros [x H].
  destruct H as [HnS [HnC HnI]].
  destruct (structural_trichotomy x)
    as [[Hs | [Hc | Hi]] [Hsc [Hsi Hci]]].
  - apply HnS; exact Hs.
  - apply HnC; exact Hc.
  - apply HnI; exact Hi.
Qed.

(* ===================================================== *)
(* === No overlap of regimes                           === *)
(* ===================================================== *)

Theorem no_regime_overlap :
  ~ (exists x : Config,
       (Stable x /\ Critical x)
    \/ (Stable x /\ Isolating x)
    \/ (Critical x /\ Isolating x)).
Proof.
  intros [x H].
  destruct (structural_trichotomy x)
    as [_ [Hsc [Hsi Hci]]].
  destruct H as [[Hs Hc] | [[Hs Hi] | [Hc Hi]]].
  - apply Hsc; split; assumption.
  - apply Hsi; split; assumption.
  - apply Hci; split; assumption.
Qed.

(* ===================================================== *)
(* === Epistemic closure                               === *)
(* ===================================================== *)

(*
  Status of results:
  - The trichotomy cannot be bypassed.
  - No configuration can escape classification.
  - No mixed or intermediate regime exists.

  These are negative, rigidity-type results.
*)

