(**
  CANON_Decision_Uniqueness.v

  F4.2 — Unicità della decisione CANON (versione CANON-safe)

  La relazione decides è funzionale:
  una metrica non può soddisfare due decisioni diverse.

  - solo inversione strutturale
  - nessun lemma esterno
  - nessuna dipendenza SHADOW
*)

From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Structure
  Loventre_LMetrics_Phase_CANON.

From Loventre_Main Require Import
  CANON_Decision_Core.

Import Loventre_LMetrics_Phase_CANON.

(* ================================================= *)
(* === Unicità strutturale della decisione        === *)
(* ================================================= *)

Theorem CANON_decision_unique :
  forall (m : LMetrics) (d1 d2 : CANON_Decision),
    decides m d1 ->
    decides m d2 ->
    d1 = d2.
Proof.
  intros m d1 d2 H1 H2.
  inversion H1; inversion H2; subst; reflexivity.
Qed.

