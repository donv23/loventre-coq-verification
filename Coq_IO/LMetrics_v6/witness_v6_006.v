(** Loventre Engine — witness_v6_006
    Tab leggera v1200 — auto generato
    Conforme alle regole auree
 *)

From Stdlib Require Import Reals.
From Stdlib Require Import String.
From LMetrics_v6 Require Import LMetrics_v6_types.

Definition witness_v6_006_example : LMetrics :=
  mkLMetrics
    6.0%R      (* kappa_eff *)
    6.1%R      (* entropy_eff *)
    6.2%R      (* mass_eff *)
    6.3%R      (* inertial_idx *)
    6.4%R      (* risk_index *)
    HIGH          (* risk_class *)
    UNSAFE        (* loventre_global_decision *)
    RED           (* loventre_global_color *)
    6.5%R      (* loventre_global_score *)
    6          (* meta_label *)
    "witness_v6_006"%string.
