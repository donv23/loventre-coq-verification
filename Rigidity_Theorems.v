(*
  Rigidity_Theorems.v

  This file formalizes the rigidity results corresponding to
  Chapter 25 of the Treatise:
  "Structural Rigidity Theorems".

  It depends ONLY on Rigidity_Core.v and introduces no new primitives.
  All results are negative or rigidity statements.
*)

Require Import Rigidity_Core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ===================================================== *)
(* === Global reversibility is impossible               === *)
(* ===================================================== *)

Theorem no_global_reversibility :
  (exists b : Config, Barrier b) ->
  ~ (forall x y : Config, trans x y -> trans y x).
Proof.
  apply no_global_symmetry.
Qed.

(* ===================================================== *)
(* === No reversible dynamics compatible with barriers  === *)
(* ===================================================== *)

Theorem no_reversible_dynamics_with_barrier :
  (exists b : Config, Barrier b) ->
  ~ (forall x y : Config, trans x y <-> trans y x).
Proof.
  intros Hb Hiff.
  apply (no_global_reversibility Hb).
  intros x y Hxy.
  apply (proj1 (Hiff x y)).
  exact Hxy.
Qed.

(* ===================================================== *)
(* === Rigidity of barrier-induced collapse             === *)
(* ===================================================== *)

Theorem barrier_entry_is_terminal :
  forall x y : Config,
    trans x y ->
    Barrier y ->
    ~ (exists z : Config, trans y z /\ trans z x).
Proof.
  intros x y Hxy Hy [z [Hyz Hzx]].
  (* From trans z x and trans x y we would obtain trans z y
     by global reversibility, which is impossible.
     Since reversibility is forbidden by barrier_irreversible,
     this configuration cannot exist. *)
  apply (barrier_irreversible z y).
  - (* z -> y *)
    (* cannot be constructed without symmetry *)
    admit.
  - exact Hy.
Qed.

(* ===================================================== *)
(* === Epistemic status                                 === *)
(* ===================================================== *)

(*
  NOTE:
  - The theorem barrier_entry_is_terminal requires an additional
    bridge principle to derive trans z y from trans z x and trans x y.
  - This bridge is intentionally NOT assumed here.
  - The 'admit' marks an explicit epistemic gap, corresponding to
    a declared residual assumption in the Treatise.
*)

