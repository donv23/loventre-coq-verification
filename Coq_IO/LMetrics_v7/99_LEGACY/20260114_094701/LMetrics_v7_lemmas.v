(****************************************************
  LMetrics_v7_lemmas.v
  Lemmi minimi di sanità per LMetrics v7
  CANVAS 7 — Stato Verde
****************************************************)

From Stdlib Require Import ZArith Lia.
From Coq Require Import Utf8.

Require Import LMetrics_v7_Prelude.
Require Import LMetrics_v7_types.

Open Scope Z_scope.

(* Lemma 1 — meta_label è sempre ≥ 0 *)
Lemma meta_label_nonneg :
  forall m : LMetricsV7, 0 <= m.(meta_label).
Proof.
  intros m. unfold meta_label.
  lia.
Qed.

(* Lemma 2 — Tutti i campi sono interi Z (sanity check) *)
Lemma all_fields_are_Z :
  forall m : LMetricsV7,
    (Z * Z * Z * Z)%type.
Proof.
  intro m. exact (
    m.(kappa_eff),
    m.(entropy_eff),
    m.(V0),
    m.(meta_label)
  ).
Qed.

(* Lemma 3 — Tupla (kappa, entropy) come estrazione di test *)
Definition core_pair (m : LMetricsV7) : Z * Z :=
  (m.(kappa_eff), m.(entropy_eff)).

Lemma core_pair_correct :
  forall m : LMetricsV7,
    fst (core_pair m) = m.(kappa_eff)
    /\ snd (core_pair m) = m.(entropy_eff).
Proof.
  intro m. unfold core_pair. simpl. auto.
Qed.

Close Scope Z_scope.

