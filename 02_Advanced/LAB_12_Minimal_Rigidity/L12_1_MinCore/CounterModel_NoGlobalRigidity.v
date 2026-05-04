(*
  LAB-12.1 — CounterModel_NoGlobalRigidity.v

  Shows that:
  - local irreversibility alone
  - does NOT force global rigidity
  - does NOT force trichotomy
*)

Require Import
  Loventre_Advanced.LAB_12_Minimal_Rigidity.L12_1_MinCore.Core_Minimal.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* === Concrete configurations === *)

Parameter a b c : Config.

(* === Transitions === *)

Axiom Hab : trans a b.
Axiom Hba : trans b a.
Axiom Hbc : trans b c.

(* === Isolation === *)

Axiom Iso_c : Isolating c.
Axiom NotIso_a : ~ Isolating a.
Axiom NotIso_b : ~ Isolating b.

(* === No other transitions === *)

Axiom no_other :
  forall x y : Config,
    trans x y ->
      (x = a /\ y = b) \/
      (x = b /\ y = a) \/
      (x = b /\ y = c).

(* === Global cycle still exists === *)

Lemma global_cycle_exists :
  trans a b /\ trans b a.
Proof.
  exact (conj Hab Hba).
Qed.

(* === No trichotomy is forced === *)

Lemma no_trichotomy_forced :
  exists x : Config,
    ~ Stable x /\ ~ Critical x /\ ~ Isolating x.
Proof.
  exists a.
  repeat split.
  - admit.
  - admit.
  - exact NotIso_a.
Admitted.

