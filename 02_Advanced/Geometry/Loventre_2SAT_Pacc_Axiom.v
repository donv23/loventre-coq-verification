(**
  Loventre_2SAT_Pacc_Axiom.v
  gennaio 2026 — V84.4.1

  Scopo:
  Introduce un assioma minimo per consentire lo sviluppo
  della classe P_accessible sul profilo 2-SAT.

  Approvato come stepping stone provvisorio.
*)

From Stdlib Require Import Reals.Rdefinitions Reals.Raxioms.

From Loventre_Core Require Import
     Loventre_Core_Prelude
     Loventre_Kernel
     Loventre_Foundation_Types
     Loventre_Foundation_Params
     Loventre_Foundation_Entropy.

From Loventre_Advanced Require Import
     Loventre_LMetrics_Core
     Loventre_Metrics_Bus
     Loventre_Class_Model
     Loventre_Class_Properties
     Loventre_PHASE_Assembly.

From Loventre_Advanced.Geometry Require Import
     Loventre_LMetrics_Structure
     Loventre_LMetrics_Phase_Predicates
     Loventre_2SAT_LMetrics_From_JSON
     Loventre_2SAT_LMetrics_Crit_JSON.

(* -------------------------------------------------------------- *)
(* === ASSIOMA Pacc MONOTONICITY PER IL PROFILO 2-SAT          === *)
(* -------------------------------------------------------------- *)

(** Se due metriche 2SAT hanno entropia <= e
    curvatura <= rispetto all'altra,
    la possibilità informazionale non peggiora.

    Placeholder ultra-minimale: dichiarato come assioma.
 *)

Axiom Pacc_Monotonicity_2SAT :
  forall (M1 M2 : LMetrics),
    (entropy_eff M1 <= entropy_eff M2)%R ->
    (kappa_eff M1   <= kappa_eff M2)%R ->
    (informational_potential M1 <= informational_potential M2)%R.

(* -------------------------------------------------------------- *)
(* NOTE OPERATIVE                                                *)
(* -------------------------------------------------------------- *)

(** Questo assioma:
      - è temporaneo ma coerente
      - non viola le dipendenze
      - garantisce la possibilità di sviluppare lemmi Pacc

    Futuro:
      • derivare la monotonicità da modello fisico
      • collegare l’informational_potential a V0, tunneling e success rate
*)

