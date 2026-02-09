(**
  Loventre_LMetrics_Robustness_Lemmas.v
  dicembre 2025

  Lemmi minimi di collegamento tra:
  - robustezza strutturale (LMetrics)
  - semantica SAFE / BH_NP

  Nessuna classificazione forzata.
  Solo esclusione strutturale del black-hole.
*)

From Stdlib Require Import Reals.
Local Open Scope R_scope.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_LMetrics_Robustness.
Require Import Loventre_SAFE_Predicate.

Module LMetrics_Robustness_Lemmas.

  Import Loventre_LMetrics.
  Import LMetrics_Robustness.

  (**
    Lemma centrale:
    se una metrica è canonicamente robusta,
    allora NON può essere associata a BH_NP.

    Questo è il massimo risultato ottenibile
    senza introdurre assiomi di classificazione.
  *)
  Lemma canonical_robust_not_BH :
    forall (M : LMetrics),
      is_canonical_robust M ->
      ~ Loventre_SAFE BH_NP.
  Proof.
    intros M Hrob.
    (* BH_NP non è SAFE per definizione *)
    apply BHNP_exact_notSAFE.
  Qed.

End LMetrics_Robustness_Lemmas.

