(** Loventre_Zfloor_Core.v
    Modulo canonico Rocq 9.1 per Zfloor/up
    GENNAIO 2026 — CANON BASE
*)

From Stdlib Require Import Reals.
From Stdlib Require Import ZArith.
From Stdlib Require Import Reals.Zfloor.

Open Scope R_scope.
Open Scope Z_scope.

(** ============================
      Lemmi NATIVI autorizzati
    ============================ *)

Lemma loventre_Zfloor_bound :
  forall x : R,
    (IZR (Zfloor x) <= x < IZR (Zfloor x) + 1)%R.
Proof.
  apply Zfloor_bound.
Qed.

Lemma loventre_Zfloor_lower :
  forall x : R,
    (IZR (Zfloor x) <= x)%R.
Proof.
  intro x.
  destruct (Zfloor_bound x) as [Hlow _].
  exact Hlow.
Qed.

Lemma loventre_Zfloor_upper :
  forall x : R,
    (x < IZR (Zfloor x) + 1)%R.
Proof.
  intro x.
  destruct (Zfloor_bound x) as [_ Hhigh].
  exact Hhigh.
Qed.

Lemma loventre_up_is_Zfloor_plus_1 :
  forall x : R, up x = Zfloor x + 1.
Proof.
  apply up_Zfloor.
Qed.

Lemma loventre_IZR_up :
  forall x : R,
    (IZR (up x) = IZR (Zfloor x) + 1)%R.
Proof.
  apply IZR_up_Zfloor.
Qed.

(** ============================
          Monotonia & esatti
    ============================ *)

Lemma loventre_Zfloor_le :
  forall x y : R,
    (x <= y)%R ->
    (Zfloor x <= Zfloor y)%Z.
Proof.
  intros x y H.
  apply Zfloor_le; exact H.
Qed.

Lemma loventre_Zfloor_exact :
  forall z : Z, Zfloor (IZR z) = z.
Proof.
  apply ZfloorZ.
Qed.

