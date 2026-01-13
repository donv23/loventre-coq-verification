(** Loventre_Zfloor_Compat_RNZ.v
    Bridge Rocq 9.1 tra Reals, Z e nat per Zfloor / up.
    FIX 15 — versione stabile con prova semplificata di R_of_nat_ge0.
 *)

From Stdlib Require Import Reals ZArith Lia Zfloor.
Open Scope R_scope.
Open Scope Z_scope.

(** Conversione sicura nat -> R via Z *)
Definition R_of_nat (n : nat) : R := IZR (Z.of_nat n).

Lemma R_of_nat_ge0 :
  forall n : nat, (0 <= R_of_nat n)%R.
Proof.
  intro n.
  unfold R_of_nat.
  (* Poiché Z.of_nat n è sempre >= 0, IZR preserva l'ordine *)
  assert (H : (0 <= Z.of_nat n)%Z) by lia.
  apply IZR_le.
  exact H.
Qed.

(** Compatibilità con Zfloor e up in Rocq 9.1 *)

Lemma Zfloor_R_of_nat :
  forall n : nat, Zfloor (R_of_nat n) = Z.of_nat n.
Proof.
  intro n.
  unfold R_of_nat.
  rewrite (ZfloorZ (Z.of_nat n)).
  reflexivity.
Qed.

Lemma up_R_of_nat :
  forall n : nat, up (R_of_nat n) = Z.of_nat n + 1.
Proof.
  intro n.
  unfold R_of_nat.
  rewrite up_Zfloor.
  rewrite (ZfloorZ (Z.of_nat n)).
  lia.
Qed.

