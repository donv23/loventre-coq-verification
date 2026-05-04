(*
  Rigidity_Theorems.v

  Formalization of Chapter 25:
  Structural Rigidity Theorems.

  Depends ONLY on Rigidity_Core.v.
*)

Require Import Loventre_Advanced.Structural_Rigidity.Rigidity_Core.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ===================================================== *)
(* === No reversibility at a barrier                   === *)
(* ===================================================== *)

Theorem no_reversibility_at_barrier :
  forall x y : Config,
    trans x y ->
    Barrier y ->
    ~ trans y x.
Proof.
  intros x y Hxy Hy.
  exact (@local_irreversibility x y Hxy Hy).
Qed.

(* ===================================================== *)
(* === Impossibility of global reversibility            === *)
(* ===================================================== *)

Theorem no_global_reversibility :
  (exists x y : Config, trans x y /\ Barrier y) ->
  ~ (forall a b : Config, trans a b -> trans b a).
Proof.
  intros [x [y [Hxy Hy]]] Hsym.
  apply (@no_reversibility_at_barrier x y Hxy Hy).
  apply Hsym.
  exact Hxy.
Qed.

(*
  Epistemic status:
  - No new axioms introduced.
  - Global rigidity follows from existence of at least
    one real barrier transition.
*)

