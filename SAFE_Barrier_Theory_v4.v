(**
  SAFE_Barrier_Theory_v4.v
  dicembre 2025 — modulo v4 della teoria coerente e stabile
*)

From Coq Require Import Reals.

(* Importiamo struttura *)
Require Import SAFE_Barrier_Structure.
Import SAFE_Barrier.

Module SAFE_Barrier_Theory_v4.

  Definition barrier_is_SAFE (B : SAFE_Barrier_Structure) : Prop :=
    barrier_V0 B = 0%R.

  Definition barrier_is_BLACKHOLE (B : SAFE_Barrier_Structure) : Prop :=
    barrier_V0 B <> 0%R.

  Definition is_SAFE_barrier (B : SAFE_Barrier_Structure) : Prop :=
    barrier_is_SAFE B.

  Definition is_BLACKHOLE_barrier (B : SAFE_Barrier_Structure) : Prop :=
    barrier_is_BLACKHOLE B.

  Lemma safe_or_blackhole_exclusion :
    forall B : SAFE_Barrier_Structure,
      is_SAFE_barrier B \/ is_BLACKHOLE_barrier B.
  Proof.
    intros B.
    unfold is_SAFE_barrier, is_BLACKHOLE_barrier,
           barrier_is_SAFE, barrier_is_BLACKHOLE.
    destruct (Req_dec (barrier_V0 B) 0%R).
    - left; auto.
    - right; auto.
  Qed.

  Lemma safe_not_blackhole :
    forall B : SAFE_Barrier_Structure,
      is_SAFE_barrier B -> ~ is_BLACKHOLE_barrier B.
  Proof.
    intros B H V.
    unfold is_SAFE_barrier, is_BLACKHOLE_barrier,
           barrier_is_SAFE, barrier_is_BLACKHOLE in *.
    subst.
    unfold not.
    intros Contra.
    apply Contra.
    reflexivity.
  Qed.

  Lemma blackhole_not_safe :
    forall B : SAFE_Barrier_Structure,
      is_BLACKHOLE_barrier B -> ~ is_SAFE_barrier B.
  Proof.
    intros B H V.
    unfold is_SAFE_barrier, is_BLACKHOLE_barrier,
           barrier_is_SAFE, barrier_is_BLACKHOLE in *.
    congruence.
  Qed.

  Definition barrier_le (B1 B2 : SAFE_Barrier_Structure) : Prop :=
    True.

  Lemma barrier_le_refl :
    forall B : SAFE_Barrier_Structure,
      barrier_le B B.
  Proof.
    intros B. unfold barrier_le. trivial.
  Qed.

  Lemma barrier_le_trans :
    forall B1 B2 B3 : SAFE_Barrier_Structure,
      barrier_le B1 B2 ->
      barrier_le B2 B3 ->
      barrier_le B1 B3.
  Proof.
    intros B1 B2 B3 H12 H23.
    unfold barrier_le; trivial.
  Qed.

  Lemma barrier_V0_discrete :
    forall B : SAFE_Barrier_Structure,
      is_SAFE_barrier B \/ is_BLACKHOLE_barrier B.
  Proof.
    intros B.
    apply safe_or_blackhole_exclusion.
  Qed.

End SAFE_Barrier_Theory_v4.

