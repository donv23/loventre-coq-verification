(**
  Loventre_LMetrics_Structure.v
  dicembre 2025 — versione v5.0 stabile finale
*)

From Stdlib Require Import Reals.Rdefinitions Reals.Raxioms.

(* ================================ *)
(* === Record LMetrics v5.0     === *)
(* ================================ *)

Record LMetrics := {
  (* metriche canoniche *)
  kappa_eff    : R;
  entropy_eff  : R;
  V0           : R;
  p_tunnel     : R;
  P_success    : R;

  (* diagnostica SAFE/BLACKHOLE (placeholder) *)
  barrier_tag  : R;

  (* v5.0 — informazione informazionale (placeholder diagnostico) *)
  informational_potential : R
}.

(* --------------------------------------------------------------- *)
(* v5.0 — Proprietà diagnostica coerente                           *)
(* --------------------------------------------------------------- *)

Definition InformationalPotentialNonneg (M : LMetrics) : Prop :=
  Rge (informational_potential M) 0%R.

Axiom informational_potential_nonneg :
  forall M : LMetrics,
    InformationalPotentialNonneg M.

