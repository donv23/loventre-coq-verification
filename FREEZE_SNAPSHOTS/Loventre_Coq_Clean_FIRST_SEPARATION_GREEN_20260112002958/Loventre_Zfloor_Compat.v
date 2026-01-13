(** Loventre_Zfloor_Compat.v
    Compatibilità Zfloor per Rocq 9.1 — monotonia e bound
    CANON V50 — gennaio 2026
*)

From Stdlib Require Import Reals ZArith Reals.Zfloor Lia.

Open Scope R_scope.
Open Scope Z_scope.

(**
  Monotonia minimale: prende direttamente Zfloor_le,
  che è nativo in Reals.Zfloor, evitando derivazioni.
*)
Lemma Loventre_Zfloor_le :
  forall x y : R,
    (x <= y)%R ->
    (Zfloor x <= Zfloor y)%Z.
Proof.
  intros x y Hxy.
  apply Zfloor_le; exact Hxy.
Qed.

(**
  Bound inferiore: il floor è <= del reale.
*)
Lemma Loventre_Zfloor_lower :
  forall x : R,
    (IZR (Zfloor x) <= x)%R.
Proof.
  intro x.
  pose proof (Zfloor_bound x) as [Hlb _].
  exact Hlb.
Qed.

(**
  Bound superiore aperto: il reale è < floor + 1
*)
Lemma Loventre_Zfloor_upper :
  forall x : R,
    (x < IZR (Zfloor x) + 1)%R.
Proof.
  intro x.
  pose proof (Zfloor_bound x) as [_ Hub].
  exact Hub.
Qed.

(**
  Trappola completa
*)
Lemma Loventre_Zfloor_trap :
  forall x : R,
    (IZR (Zfloor x) <= x < IZR (Zfloor x) + 1)%R.
Proof.
  intro x.
  apply Zfloor_bound.
Qed.

