(*
  Test_CANON_Separation.v
  STEP 2 — Kernel stress test for non-reconstructive separation
*)

(* ======================= *)
(* Primitive global notions *)
(* ======================= *)

Parameter Config : Type.

(* Global basins as predicates *)
Definition Basin := Config -> Prop.

(* Observations: deliberately non-invertible *)
Parameter Obs : Type.
Parameter observe : Config -> Obs.

(* Barrier as primitive structural separation *)
Parameter Barrier : Basin -> Basin -> Prop.

(* Global transformations *)
Parameter Transform : Type.
Parameter apply : Transform -> Basin -> Basin.

(* Structural equivalence via admissible transformations *)
Definition StructEquiv (B1 B2 : Basin) : Prop :=
  exists T : Transform, apply T B1 = B2.

(* Total observational indistinguishability *)
Definition ObsIndist (B1 B2 : Basin) : Prop :=
  forall x y : Config,
    B1 x -> B2 y -> observe x = observe y.

(* ======================= *)
(* Separation theorem      *)
(* ======================= *)

Axiom Structural_Separation :
  exists B1 B2 : Basin,
    B1 <> B2 /\
    Barrier B1 B2 /\
    ObsIndist B1 B2 /\
    ~ StructEquiv B1 B2.

(* ======================= *)
(* What MUST NOT be provable *)
(* ======================= *)

(* This is intentionally left unprovable.
   Any proof of this requires an explicit reconstruction axiom. *)

Goal forall B1 B2 : Basin,
  ObsIndist B1 B2 -> StructEquiv B1 B2.
Abort.

(* ======================= *)
(* Optional: explicit reconstruction axiom *)
(* Uncommenting this would collapse the theorem *)
(*
Axiom Observational_Extensionality :
  forall B1 B2 : Basin,
    ObsIndist B1 B2 -> B1 = B2.
*)

