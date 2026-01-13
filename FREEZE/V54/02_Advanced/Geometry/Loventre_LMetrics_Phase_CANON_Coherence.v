(**
  Loventre_LMetrics_Phase_CANON_Coherence.v

  Lemmi di coerenza minimale per la semantica di fase CANON.

  Questo file:
  - non è importato dal CANON v3
  - non entra nel Main
  - non modifica il grafo esistente
  - dimostra solo non-contraddizione

  Dicembre 2025
*)

From Stdlib Require Import
  Reals.Rdefinitions
  Reals.Raxioms
  Lra.

From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Structure
  Loventre_LMetrics_Phase_CANON.

Import Loventre_LMetrics_Phase_CANON.

(* ===================================================== *)
(* === Lemmi di coerenza                               === *)
(* ===================================================== *)

Lemma SAFE_not_BLACKHOLE :
  forall m : LMetrics,
    is_SAFE m -> ~ is_BLACKHOLE m.
Proof.
  intros m Hsafe.
  unfold is_SAFE, is_BLACKHOLE in *.
  intros [Hpt Hps].
  destruct Hsafe as [Hpt_safe Hps_safe].
  lra.
Qed.

