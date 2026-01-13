(**
  Loventre_LMetrics_Phase_CANON_Lemmas.v

  Lemmi di coerenza minimale per le fasi CANON.
  File shadow, non importato dal progetto principale.

  Dicembre 2025
*)

From Stdlib Require Import
  Reals.Rdefinitions
  Reals.Raxioms
  Lra.

From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Structure
  Loventre_LMetrics_Phase_CANON_Index.

Import Loventre_LMetrics_Phase_CANON.

(* ===================================================== *)
(* === Lemmi di sanità minimale                        === *)
(* ===================================================== *)

Lemma SAFE_not_BLACKHOLE :
  forall m : LMetrics,
    is_SAFE m -> ~ is_BLACKHOLE m.
Proof.
  intros m Hsafe Hbh.
  unfold is_SAFE, is_BLACKHOLE in *.
  destruct Hsafe as [Hpt Hps].
  destruct Hbh as [Hptb Hpsb].
  lra.
Qed.

