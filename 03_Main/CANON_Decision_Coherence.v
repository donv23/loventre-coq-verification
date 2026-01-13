(**
  CANON_Decision_Coherence.v

  FASE F2 — Coerenza decisionale CANON (LOGICA)

  Qui NON costruiamo una decisione computazionale,
  ma dimostriamo che la fase CANON determina
  una decisione logica coerente.

  Nessuna eliminazione Prop → Set.
  Nessuna logica classica.
  Nessun assioma.

  Dicembre 2025
*)

From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Structure
  Loventre_LMetrics_Phase_CANON_Index.

Import Loventre_LMetrics_Phase_CANON.

(* =============================================== *)
(* === Predicato di decisione CANON             === *)
(* =============================================== *)

Inductive CANON_Decision (m : LMetrics) : Prop :=
  | Decide_SAFE :
      is_SAFE m -> CANON_Decision m
  | Decide_WARNING :
      is_WARNING m -> CANON_Decision m
  | Decide_BLACKHOLE :
      is_BLACKHOLE m -> CANON_Decision m.

(* =============================================== *)
(* === Teorema di coerenza decisionale           === *)
(* =============================================== *)

Theorem CANON_decision_coherent :
  forall m : LMetrics,
    is_SAFE m \/ is_WARNING m \/ is_BLACKHOLE m ->
    CANON_Decision m.
Proof.
  intros m H.
  destruct H as [Hsafe | [Hwarn | Hbh]].
  - apply Decide_SAFE; exact Hsafe.
  - apply Decide_WARNING; exact Hwarn.
  - apply Decide_BLACKHOLE; exact Hbh.
Qed.

