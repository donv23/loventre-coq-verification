(** Loventre Engine — witness_v6_047
    Tab leggera v1200 — auto generato
    Conforme alle regole auree
 *)

From Stdlib Require Import Reals.
From Stdlib Require Import String.
From LMetrics_v6 Require Import LMetrics_v6_types.

Definition witness_v6_047_example : LMetrics :=
  mkLMetrics
    47.0%R      (* kappa_eff *)
    47.1%R      (* entropy_eff *)
    47.2%R      (* mass_eff *)
    47.3%R      (* inertial_idx *)
    47.4%R      (* risk_index *)
    HIGH          (* risk_class *)
    UNSAFE        (* loventre_global_decision *)
    RED           (* loventre_global_color *)
    47.5%R      (* loventre_global_score *)
    47          (* meta_label *)
    "witness_v6_047"%string.
