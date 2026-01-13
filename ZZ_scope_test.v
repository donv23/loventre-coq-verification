Lemma test_Rscope_explicit :
  forall x:R,
    (IZR (Zfloor x) <= x)%R.
From Stdlib Require Import Reals ZArith Zfloor.

Open Scope R_scope.
Open Scope Z_scope.

Lemma test_mix :
  forall x:R,
    (IZR (Zfloor x) <= x).
Proof.
  intro x.
  pose proof (Zfloor_floor_lb x) as H.
  lra.
Qed.

