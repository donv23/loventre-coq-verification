(** Loventre Engine — witness_v6_013
    Tab leggera v1200 — auto generato
    Conforme alle regole auree
 *)

From Stdlib Require Import Reals.
From Stdlib Require Import String.
From LMetrics_v6 Require Import LMetrics_v6_types.

Definition witness_v6_013_example : LMetrics :=
  mkLMetrics
    13.0%R      (* kappa_eff *)
    13.1%R      (* entropy_eff *)
    13.2%R      (* mass_eff *)
    13.3%R      (* inertial_idx *)
    13.4%R      (* risk_index *)
    HIGH          (* risk_class *)
    UNSAFE        (* loventre_global_decision *)
    RED           (* loventre_global_color *)
    13.5%R      (* loventre_global_score *)
    13          (* meta_label *)
    "witness_v6_013"%string.
