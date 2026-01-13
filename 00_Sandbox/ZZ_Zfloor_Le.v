(**
  ZZ_Zfloor_Le.v
  Lemma sandbox: monotonia di Zfloor in Rocq 9.1.
*)

From Stdlib Require Import Reals ZArith Psatz Lia Zfloor.

Open Scope R_scope.

Lemma loventre_Zfloor_le :
  forall x y : R,
    (x <= y)%R ->
    Zfloor x <= Zfloor y.
Proof.
  intros x y Hxy.
  apply Zfloor_le; exact Hxy.
Qed.

Print Assumptions loventre_Zfloor_le.

