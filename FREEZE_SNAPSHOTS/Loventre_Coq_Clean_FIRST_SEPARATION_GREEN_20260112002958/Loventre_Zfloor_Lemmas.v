(** Loventre_Zfloor_Lemmas.v
    Lemmi di base su Zfloor in Rocq 9.1/Coq 9.
 *)

From Stdlib Require Import Reals ZArith Psatz Zfloor.
Open Scope R_scope.

(** === Lemmi nativi Rocq 9.1 === *)

(** Monotonia *)
Lemma Zfloor_mono :
  forall x y : R,
    (x <= y)%R ->
    (Zfloor x <= Zfloor y)%Z.
Proof.
  intros x y Hxy.
  apply Zfloor_le; exact Hxy.
Qed.

Lemma Zfloor_strict_mono :
  forall x y : R,
    (x < y)%R ->
    (Zfloor x <= Zfloor y)%Z.
Proof.
  intros x y Hxy.
  apply Zfloor_le.
  apply Rlt_le; exact Hxy.
Qed.

(** Bound inferiore *)
Lemma Zfloor_lower_bound :
  forall x : R,
    (IZR (Zfloor x) <= x)%R.
Proof.
  intro x.
  pose proof (Zfloor_bound x) as [Hlow _].
  exact Hlow.
Qed.

(** Bound superiore aperto *)
Lemma Zfloor_upper_open :
  forall x : R,
    (x < IZR (Zfloor x) + 1)%R.
Proof.
  intro x.
  pose proof (Zfloor_bound x) as [_ Hhigh].
  exact Hhigh.
Qed.

(** Pacchetto completo: “trappola” *)
Lemma Zfloor_trap :
  forall x : R,
    (IZR (Zfloor x) <= x < IZR (Zfloor x) + 1)%R.
Proof.
  intro x; apply Zfloor_bound.
Qed.

