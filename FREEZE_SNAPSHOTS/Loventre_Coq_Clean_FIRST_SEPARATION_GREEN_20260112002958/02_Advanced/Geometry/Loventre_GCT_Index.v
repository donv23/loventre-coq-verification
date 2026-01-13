(*
  Loventre_GCT_Index.v
  ============================================================

  GLOBAL COHERENCE TRICHOTOMY (GCT) — PUBLIC INDEX

  This file is the OFFICIAL ENTRY POINT for the GCT framework.

  It:
  - introduces NO new axioms
  - introduces NO new parameters
  - contains NO admitted proofs
  - re-exports only structural vocabulary

  Any file importing GCT should import THIS file,
  and not the internal components directly.
*)

(* ------------------------------------------------------------ *)
(* GCT structural vocabulary                                    *)
(* ------------------------------------------------------------ *)

Require Export Loventre_Advanced.Geometry.Loventre_GCT_Signature.

(* ------------------------------------------------------------ *)
(* GCT structural barriers                                      *)
(* ------------------------------------------------------------ *)

Require Export Loventre_Advanced.Geometry.Loventre_GCT_Conductance.
Require Export Loventre_Advanced.Geometry.Loventre_GCT_Coupling.
Require Export Loventre_Advanced.Geometry.Loventre_GCT_Monodromy.

(* ------------------------------------------------------------ *)
(* GCT global classification principle                           *)
(* ------------------------------------------------------------ *)

Require Export Loventre_Advanced.Geometry.Loventre_GCT_Trichotomy.

