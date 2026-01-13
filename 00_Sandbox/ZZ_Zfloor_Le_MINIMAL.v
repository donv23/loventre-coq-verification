From Stdlib Require Import Reals ZArith Zfloor.

Open Scope R_scope.

Lemma loventre_Zfloor_le_MINIMAL :
  forall x y : R,
    (x <= y)%R ->
    Zfloor x <= Zfloor y.
Proof.
  apply Zfloor_le.
Qed.

