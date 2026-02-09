(** Loventre Engine — witness_v6_002
    Tab leggera v1200 — auto generato
    Conforme alle regole auree
 *)

From Stdlib Require Import Reals.
From Stdlib Require Import String.
From LMetrics_v6 Require Import LMetrics_v6_types.

Definition witness_v6_002_example : LMetrics :=
  mkLMetrics
    2.0%R      (* kappa_eff *)
    2.1%R      (* entropy_eff *)
    2.2%R      (* mass_eff *)
    2.3%R      (* inertial_idx *)
    2.4%R      (* risk_index *)
    HIGH          (* risk_class *)
    UNSAFE        (* loventre_global_decision *)
    RED           (* loventre_global_color *)
    2.5%R      (* loventre_global_score *)
    2          (* meta_label *)
    "witness_v6_002"%string.
