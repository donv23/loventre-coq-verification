(** Loventre Engine — witness_v6_048
    Tab leggera v1200 — auto generato
    Conforme alle regole auree
 *)

From Stdlib Require Import Reals.
From Stdlib Require Import String.
From LMetrics_v6 Require Import LMetrics_v6_types.

Definition witness_v6_048_example : LMetrics :=
  mkLMetrics
    48.0%R      (* kappa_eff *)
    48.1%R      (* entropy_eff *)
    48.2%R      (* mass_eff *)
    48.3%R      (* inertial_idx *)
    48.4%R      (* risk_index *)
    HIGH          (* risk_class *)
    UNSAFE        (* loventre_global_decision *)
    RED           (* loventre_global_color *)
    48.5%R      (* loventre_global_score *)
    48          (* meta_label *)
    "witness_v6_048"%string.
