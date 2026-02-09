(** Loventre Engine — witness_v6_032
    Tab leggera v1200 — auto generato
    Conforme alle regole auree
 *)

From Stdlib Require Import Reals.
From Stdlib Require Import String.
From LMetrics_v6 Require Import LMetrics_v6_types.

Definition witness_v6_032_example : LMetrics :=
  mkLMetrics
    32.0%R      (* kappa_eff *)
    32.1%R      (* entropy_eff *)
    32.2%R      (* mass_eff *)
    32.3%R      (* inertial_idx *)
    32.4%R      (* risk_index *)
    HIGH          (* risk_class *)
    UNSAFE        (* loventre_global_decision *)
    RED           (* loventre_global_color *)
    32.5%R      (* loventre_global_score *)
    32          (* meta_label *)
    "witness_v6_032"%string.
