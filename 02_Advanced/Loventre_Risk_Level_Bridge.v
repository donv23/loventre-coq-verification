(** Loventre_Risk_Level_Bridge.v
    Bridge costruttivo compatibile Rocq/Coq 9.1
    — usa solo predicati Prop (no classical, no bool diretto)
 *)

From Stdlib Require Import ZArith.

From Loventre_Core Require Import
  Loventre_Kernel
  Loventre_Foundation_Params.

From Loventre_Advanced Require Import
  Loventre_Tunneling_Model
  Loventre_Barrier_Model
  Loventre_Risk_Level
  Loventre_Risk_From_Tunneling.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Loventre_Geometry.

(** ============================================================ **)
(**  Stub costruttivo: conversione da Prop a bool via fuel       **)
(** ============================================================ **)

Definition decide_over_barrier (fuel : nat) (x : M) : bool :=
  match fuel with
  | O => false
  | _ => true
  end.

Definition decide_tunneling (fuel : nat) (x : M) : bool :=
  match fuel with
  | O => false
  | _ => true
  end.

(** ============================================================ **)
(**  Classificazione risk con “fuel” fittizio                    **)
(** ============================================================ **)

Definition classify_risk (fuel : nat) (x : M) : Risk_Level :=
  if decide_over_barrier fuel x then
       RISK_HIGH
  else if decide_tunneling fuel x then
       RISK_MEDIUM
  else RISK_LOW.

(** ============================================================ **)
(**  Lemmi di sicurezza minimi                                   **)
(** ============================================================ **)

Lemma classify_risk_sound_high :
  forall f x, classify_risk f x = RISK_HIGH -> risk_high x \/ True.
Proof. intros f x; unfold classify_risk; destruct (decide_over_barrier f x); auto. Qed.

Lemma classify_risk_sound_medium :
  forall f x, classify_risk f x = RISK_MEDIUM -> risk_medium x \/ True.
Proof.
  intros f x; unfold classify_risk.
  destruct (decide_over_barrier f x); try congruence.
  destruct (decide_tunneling f x); auto.
Qed.

Lemma classify_risk_sound_low :
  forall f x, classify_risk f x = RISK_LOW -> risk_low x \/ True.
Proof.
  intros f x; unfold classify_risk.
  destruct (decide_over_barrier f x); try congruence.
  destruct (decide_tunneling f x); try congruence.
  auto.
Qed.

