(** Loventre Engine — witness_v6_012
    Tab leggera v1200 — auto generato
    Conforme alle regole auree
 *)

From Stdlib Require Import Reals.
From Stdlib Require Import String.
From LMetrics_v6 Require Import LMetrics_v6_types.

Definition witness_v6_012_example : LMetrics :=
  mkLMetrics
    12.0%R      (* kappa_eff *)
    12.1%R      (* entropy_eff *)
    12.2%R      (* mass_eff *)
    12.3%R      (* inertial_idx *)
    12.4%R      (* risk_index *)
    HIGH          (* risk_class *)
    UNSAFE        (* loventre_global_decision *)
    RED           (* loventre_global_color *)
    12.5%R      (* loventre_global_score *)
    12          (* meta_label *)
    "witness_v6_012"%string.
