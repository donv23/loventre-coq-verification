(** Loventre Engine — witness_v6_007
    Tab leggera v1200 — auto generato
    Conforme alle regole auree
 *)

From Stdlib Require Import Reals.
From Stdlib Require Import String.
From LMetrics_v6 Require Import LMetrics_v6_types.

Definition witness_v6_007_example : LMetrics :=
  mkLMetrics
    7.0%R      (* kappa_eff *)
    7.1%R      (* entropy_eff *)
    7.2%R      (* mass_eff *)
    7.3%R      (* inertial_idx *)
    7.4%R      (* risk_index *)
    HIGH          (* risk_class *)
    UNSAFE        (* loventre_global_decision *)
    RED           (* loventre_global_color *)
    7.5%R      (* loventre_global_score *)
    7          (* meta_label *)
    "witness_v6_007"%string.
