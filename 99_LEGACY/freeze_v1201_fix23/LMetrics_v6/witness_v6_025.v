(** Loventre Engine — witness_v6_025
    Tab leggera v1200 — auto generato
    Conforme alle regole auree
 *)

From Stdlib Require Import Reals.
From Stdlib Require Import String.
From LMetrics_v6 Require Import LMetrics_v6_types.

Definition witness_v6_025_example : LMetrics :=
  mkLMetrics
    25.0%R      (* kappa_eff *)
    25.1%R      (* entropy_eff *)
    25.2%R      (* mass_eff *)
    25.3%R      (* inertial_idx *)
    25.4%R      (* risk_index *)
    HIGH          (* risk_class *)
    UNSAFE        (* loventre_global_decision *)
    RED           (* loventre_global_color *)
    25.5%R      (* loventre_global_score *)
    25          (* meta_label *)
    "witness_v6_025"%string.
