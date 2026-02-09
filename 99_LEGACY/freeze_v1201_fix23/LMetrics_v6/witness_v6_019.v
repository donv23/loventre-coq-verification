(** Loventre Engine — witness_v6_019
    Tab leggera v1200 — auto generato
    Conforme alle regole auree
 *)

From Stdlib Require Import Reals.
From Stdlib Require Import String.
From LMetrics_v6 Require Import LMetrics_v6_types.

Definition witness_v6_019_example : LMetrics :=
  mkLMetrics
    19.0%R      (* kappa_eff *)
    19.1%R      (* entropy_eff *)
    19.2%R      (* mass_eff *)
    19.3%R      (* inertial_idx *)
    19.4%R      (* risk_index *)
    HIGH          (* risk_class *)
    UNSAFE        (* loventre_global_decision *)
    RED           (* loventre_global_color *)
    19.5%R      (* loventre_global_score *)
    19          (* meta_label *)
    "witness_v6_019"%string.
