(** Loventre Engine — witness_v6_030
    Tab leggera v1200 — auto generato
    Conforme alle regole auree
 *)

From Stdlib Require Import Reals.
From Stdlib Require Import String.
From LMetrics_v6 Require Import LMetrics_v6_types.

Definition witness_v6_030_example : LMetrics :=
  mkLMetrics
    30.0%R      (* kappa_eff *)
    30.1%R      (* entropy_eff *)
    30.2%R      (* mass_eff *)
    30.3%R      (* inertial_idx *)
    30.4%R      (* risk_index *)
    HIGH          (* risk_class *)
    UNSAFE        (* loventre_global_decision *)
    RED           (* loventre_global_color *)
    30.5%R      (* loventre_global_score *)
    30          (* meta_label *)
    "witness_v6_030"%string.
