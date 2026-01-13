(** Loventre_Zfloor_Mono.v
    Monotonia di Zfloor in Rocq 9.1 — versione formale pulita.
 *)

From Stdlib Require Import Reals ZArith Psatz Zfloor.
Open Scope R_scope.

(** Rocq 9.1: lemma nativo:
      Zfloor_le :
        forall x y : R,
        (x <= y)%R ->
        (Zfloor x <= Zfloor y)%Z
 *)

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

Lemma Zfloor_lower_bound :
  forall x : R,
    (IZR (Zfloor x) <= x)%R.
Proof.
  intro x.
  (* Zfloor_bound:
       IZR (Zfloor x) <= x < IZR (Zfloor x) + 1
   *)
  pose proof (Zfloor_bound x) as Hb.
  tauto.
Qed.

