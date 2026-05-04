(*
  LAB-15.2 — CounterModel_Not_SAFE.v

  Countermodel showing that:
  InternallyRigid does NOT imply SAFE.

  Internal rigidity is symmetric exclusion,
  SAFE requires closure.
*)

Require Import
  Loventre_Advanced.LAB_15_SAFE_Regions.L15_1_Core.Core_SAFE_Region.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* === Concrete configurations === *)

Inductive C : Type :=
| a | b | c.

Definition Config := C.

(* === Path relation (opaque for the core) === *)

Inductive pathM : Config -> Config -> Prop :=
| Hab : pathM a b
| Hbc : pathM b c.

Definition path := pathM.

(* === Transition (unused) === *)

Definition trans (x y : Config) : Prop := False.

(* === Region: only a and b === *)

Definition Region (x : Config) : Prop :=
  x = a \/ x = b.

(* === Internal rigidity HOLDS === *)

Lemma InternallyRigid_holds : InternallyRigid.
Proof.
  unfold InternallyRigid, internal_path.
  intros x y Hxy Hyx.

  destruct Hxy as [Hxy_path [Hx Hy]].
  destruct Hyx as [Hyx_path [Hy' Hx']].

  (* Case analysis on region membership *)
  destruct Hx as [Hx | Hx];
  destruct Hy as [Hy | Hy];
  destruct Hy' as [Hy' | Hy'];
  destruct Hx' as [Hx' | Hx'];
  subst; discriminate.
Qed.

(* === PathClosed FAILS === *)

Lemma not_PathClosed : ~ PathClosed.
Proof.
  unfold PathClosed.
  intro H.

  specialize (H b c).
  assert (Region b) by (right; reflexivity).

  specialize (H H0 Hbc).
  destruct H; discriminate.
Qed.

(* === Therefore SAFE fails === *)

Lemma not_SAFE : ~ SAFE.
Proof.
  unfold SAFE.
  intro H.
  destruct H as [_ HC].
  apply not_PathClosed.
  exact HC.
Qed.

