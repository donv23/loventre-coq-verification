(** Loventre_Zfloor_Migrate_Core.v
    Migrazione minimal Zfloor/ceil per Rocq 9.1
    Tutto ciò che segue è garantito esistente in Stdlib.Reals.Zfloor
 *)

From Stdlib Require Import
  Reals
  ZArith
  Psatz
  Zfloor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Open Scope R_scope.
Open Scope Z_scope.

Section Zfloor_Migrate.

  Variable x y : R.

  (** === Lemmi che sostituiscono i vecchi equivalenti 8.x === *)

  (** 1. Zfloor corrisponde al bound inferiore *)
  Lemma loventre_Zfloor_lb :
    (IZR (Zfloor x) <= x)%R.
  Proof.
    apply (proj1 (Zfloor_bound x)).
  Qed.

  (** 2. Bound completo floor: [floor x <= x < floor x + 1] *)
  Lemma loventre_Zfloor_bound :
    (IZR (Zfloor x) <= x < IZR (Zfloor x) + 1)%R.
  Proof.
    apply Zfloor_bound.
  Qed.

  (** 3. Monotonia del floor *)
  Lemma loventre_Zfloor_mono :
    (x <= y)%R ->
    (Zfloor x <= Zfloor y)%Z.
  Proof.
    intro H.
    apply Zfloor_le; exact H.
  Qed.

  (** 4. Floor + 1 = up *)
  Lemma loventre_Zfloor_up_link :
    up x = (Zfloor x + 1)%Z.
  Proof.
    apply up_Zfloor.
  Qed.

  (** 5. Parte superiore: Zceil come duale di Zfloor *)
  Lemma loventre_Zceil_dual :
    Zceil x = (- Zfloor (-x))%Z.
  Proof.
    (* In Rocq 9.1: ZceilN : forall t:R, Zceil (-t) = (- Zfloor t)%Z *)
    pose proof (ZceilN (-x)) as H.
    (* H : Zceil (- (- x)) = (- Zfloor (- x))%Z *)
    rewrite Ropp_involutive in H.
    exact H.
  Qed.

  (** 6. Caso integrale esatto *)
  Lemma loventre_ZfloorZ :
    forall z : Z, Zfloor (IZR z) = z.
  Proof.
    apply ZfloorZ.
  Qed.

End Zfloor_Migrate.

