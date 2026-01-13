From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Zfloor.

Open Scope R_scope.

(*
  Rocq 9.1 note:
  - archimed is the canonical source of floor bounds.
  - Zfloor x : Z automatically selects the integer given by archimed.
*)

Lemma Zfloor_bounds :
  forall x : R,
    (IZR (Zfloor x) <= x < IZR (Zfloor x) + 1)%R.
Proof.
  intro x.
  (* This lemma is already provided by the library *)
  apply archimed.
Qed.

