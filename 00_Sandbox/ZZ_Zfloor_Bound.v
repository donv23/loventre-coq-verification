(**
  ZZ_Zfloor_Bound.v
  Sandbox Z-layer test — Tentativo #1
  Obiettivo: usare SOLO lemmi confermati da ROCQ 9.1
*)

From Stdlib Require Import Reals ZArith Zfloor.
Require Import Psatz.

Open Scope R_scope.
Open Scope Z_scope.

(* Lemma di test: Zfloor dà sempre un bound inferiore e un bound stretto superiore *)
Lemma loventre_test_Zfloor_bound :
  forall x : R,
    (IZR (Zfloor x) <= x < IZR (Zfloor x) + 1)%R.
Proof.
  intros x.
  (* Zfloor_bound è esattamente questo lemma!
     Non c'è nulla da provare: basta applicarlo. *)
  apply Zfloor_bound.
Qed.

