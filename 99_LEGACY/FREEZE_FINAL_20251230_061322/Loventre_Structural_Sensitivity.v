(**
  Loventre_Structural_Sensitivity.v
  dicembre 2025

  Definizione della sensibilità strutturale (PSS).
*)

From Stdlib Require Import Reals.

Require Import Loventre_LMetrics_Structure.
Require Import Loventre_LMetrics_Robustness.

Import Loventre_LMetrics.
Import LMetrics_Robustness.

(**
  Una metrica è strutturalmente sensibile se:
  - è canonicamente robusta
  - NON è invariante
*)
Definition is_structurally_sensitive (M : LMetrics) : Prop :=
  is_canonical_robust M /\ ~ is_invariant M.

(**
  Ipotesi strutturale minima:
  esiste almeno una metrica
  robusta ma sensibile.

  NOTA:
  Questo NON è un assioma globale,
  ma un parametro locale del modello.
*)
Parameter exists_structurally_sensitive :
  exists M : LMetrics, is_structurally_sensitive M.

