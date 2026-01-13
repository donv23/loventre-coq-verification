(**
  CANON_Decision_Core.v

  F4.1 — Decisione CANON (forma corretta)

  La decisione NON è una funzione computazionale.
  È una relazione logica totale e coerente.

  Nessuna eliminazione Prop → Set.
  Nessun assioma.
  Coq-safe.
*)

From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Structure
  Loventre_LMetrics_Phase_CANON
  Loventre_LMetrics_Phase_CANON_Totality.

Import Loventre_LMetrics_Phase_CANON.

(* ================================ *)
(* === Tipo astratto di decisione === *)
(* ================================ *)

Inductive CANON_Decision :=
| DEC_SAFE
| DEC_WARNING
| DEC_BLACKHOLE.

(* ============================================ *)
(* === Relazione: m decide d                 === *)
(* ============================================ *)

Definition decides (m : LMetrics) (d : CANON_Decision) : Prop :=
  match d with
  | DEC_SAFE       => is_SAFE m
  | DEC_WARNING    => is_WARNING m
  | DEC_BLACKHOLE  => is_BLACKHOLE m
  end.

(* ============================================ *)
(* === Totalità della decisione CANON        === *)
(* ============================================ *)

Theorem CANON_decision_exists :
  forall m : LMetrics,
    exists d : CANON_Decision, decides m d.
Proof.
  intro m.
  destruct (CANON_totality m) as [Hsafe | [Hwarn | Hbh]].
  - exists DEC_SAFE. exact Hsafe.
  - exists DEC_WARNING. exact Hwarn.
  - exists DEC_BLACKHOLE. exact Hbh.
Qed.

