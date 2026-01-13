(**
  ZZ_Zfloor_Le_FIX1.v
  Test minimale di monotonia Zfloor.
  Versione sterile da sporco di rewriting.
*)

From Stdlib Require Import Reals ZArith Psatz Lia Zfloor.

Open Scope R_scope.

Lemma loventre_Zfloor_le_fix1 :
  forall x y : R,
    (x <= y)%R ->
    Zfloor x <= Zfloor y.
Proof.
  intros x y Hxy.
  apply Zfloor_le.
  exact Hxy.
Qed.

Print Assumptions loventre_Zfloor_le_fix1.

