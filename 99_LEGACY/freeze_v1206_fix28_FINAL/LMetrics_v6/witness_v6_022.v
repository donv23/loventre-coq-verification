(** Loventre Engine — witness_v6_022
    Tab leggera v1200 — auto generato
    Conforme alle regole auree
 *)

From Stdlib Require Import Reals.
From Stdlib Require Import String.
From LMetrics_v6 Require Import LMetrics_v6_types.

Definition witness_v6_022_example : LMetrics :=
  mkLMetrics
    22.0%R      (* kappa_eff *)
    22.1%R      (* entropy_eff *)
    22.2%R      (* mass_eff *)
    22.3%R      (* inertial_idx *)
    22.4%R      (* risk_index *)
    HIGH          (* risk_class *)
    UNSAFE        (* loventre_global_decision *)
    RED           (* loventre_global_color *)
    22.5%R      (* loventre_global_score *)
    22          (* meta_label *)
    "witness_v6_022"%string.
