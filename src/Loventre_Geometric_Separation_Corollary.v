(*
  Loventre_Geometric_Separation_Corollary.v

  This file derives a simple structural corollary
  from the geometric separation core.

  IMPORTANT:
  - No new axioms are introduced here.
  - Everything is derived from the core assumptions.
*)

From Stdlib Require Import Reals.

Require Import Loventre_Geometric_Separation.

Open Scope R_scope.

(* ------------------------------------------------------------ *)
(* Corollary: monotonic persistence of separation               *)
(* ------------------------------------------------------------ *)

(*
  Intuition (informal):

  If a geometric separation holds at some scale,
  then it also holds at any larger scale parameter,
  provided the separation predicate is monotone.
*)

Lemma geometric_separation_monotone :
  forall (scale1 scale2 : R),
    scale1 <= scale2 ->
    GeometricSeparation scale1 ->
    GeometricSeparation scale2.
Proof.
  intros scale1 scale2 Hle Hsep.
  (* This follows directly from the monotonicity
     assumption embedded in the core definition. *)
  apply GeometricSeparation_monotone with (scale1 := scale1); auto.
Qed.

(* ------------------------------------------------------------ *)
(* Corollary: robustness under scale strengthening              *)
(* ------------------------------------------------------------ *)

(*
  A direct corollary: once separation is established,
  it is robust under any finite strengthening of the scale.
*)

Lemma geometric_separation_robust :
  forall (scale delta : R),
    0 <= delta ->
    GeometricSeparation scale ->
    GeometricSeparation (scale + delta).
Proof.
  intros scale delta Hdelta Hsep.
  apply geometric_separation_monotone with (scale1 := scale); lra.
Qed.

