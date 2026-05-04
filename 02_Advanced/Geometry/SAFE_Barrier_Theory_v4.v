(**
  SAFE_Barrier_Theory_v4.v
  dicembre 2025 — modulo v4 della teoria coerente e stabile
*)

From Coq Require Import Reals.

(* Import da namespace corretto *)
Require Import Loventre_Geom.SAFE_Barrier_Structure.
Import SAFE_Barrier.

Module SAFE_Barrier_Theory_v4.

  (* ------------------------------------------------------ *)
  (* Identificatori di stato (placeholder diagnostico v4)   *)
  (* ------------------------------------------------------ *)

  Definition barrier_is_SAFE (B : SAFE_Barrier_Structure) : Prop :=
    barrier_V0 B = 0%R.

  Definition barrier_is_BLACKHOLE (B : SAFE_Barrier_Structure) : Prop :=
    barrier_V0 B <> 0%R.

  Definition is_SAFE_barrier (B : SAFE_Barrier_Structure) : Prop :=
    barrier_is_SAFE B.

  Definition is_BLACKHOLE_barrier (B : SAFE_Barrier_Structure) : Prop :=
    barrier_is_BLACKHOLE B.

  (* ------------------------------------------------------ *)
  (* Esclusione logica SAFE/BLACKHOLE                       *)
  (* ------------------------------------------------------ *)

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
    intros B Hsafe Hblack.
    unfold is_SAFE_barrier, is_BLACKHOLE_barrier,
           barrier_is_SAFE, barrier_is_BLACKHOLE in *.
    rewrite Hsafe in Hblack.
    exact (Hblack eq_refl).
  Qed.

  Lemma blackhole_not_safe :
    forall B : SAFE_Barrier_Structure,
      is_BLACKHOLE_barrier B -> ~ is_SAFE_barrier B.
  Proof.
    intros B Hblack Hsafe.
    unfold is_SAFE_barrier, is_BLACKHOLE_barrier,
           barrier_is_SAFE, barrier_is_BLACKHOLE in *.
    rewrite Hsafe in Hblack.
    exact (Hblack eq_refl).
  Qed.

  (* ------------------------------------------------------ *)
  (* Relazione placeholder (transitiva)                     *)
  (* ------------------------------------------------------ *)

  Definition barrier_le (B1 B2 : SAFE_Barrier_Structure) : Prop :=
    True.

  Lemma barrier_le_refl :
    forall B : SAFE_Barrier_Structure,
      barrier_le B B.
  Proof.
    unfold barrier_le; trivial.
  Qed.

  Lemma barrier_le_trans :
    forall B1 B2 B3 : SAFE_Barrier_Structure,
      barrier_le B1 B2 ->
      barrier_le B2 B3 ->
      barrier_le B1 B3.
  Proof.
    unfold barrier_le; trivial.
  Qed.

  (* ------------------------------------------------------ *)
  (* Mini lemma discrezione v4 (anchor per v5 Hawking)      *)
  (* ------------------------------------------------------ *)

  Lemma barrier_V0_discrete :
    forall B : SAFE_Barrier_Structure,
      is_SAFE_barrier B \/ is_BLACKHOLE_barrier B.
  Proof.
    apply safe_or_blackhole_exclusion.
  Qed.

End SAFE_Barrier_Theory_v4.

