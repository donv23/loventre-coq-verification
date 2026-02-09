(** Loventre Engine — witness_v6_061
    Tab leggera v1200 — auto generato
    Conforme alle regole auree
 *)

From Stdlib Require Import Reals.
From Stdlib Require Import String.
From LMetrics_v6 Require Import LMetrics_v6_types.

Definition witness_v6_061_example : LMetrics :=
  mkLMetrics
    61.0%R      (* kappa_eff *)
    61.1%R      (* entropy_eff *)
    61.2%R      (* mass_eff *)
    61.3%R      (* inertial_idx *)
    61.4%R      (* risk_index *)
    HIGH          (* risk_class *)
    UNSAFE        (* loventre_global_decision *)
    RED           (* loventre_global_color *)
    61.5%R      (* loventre_global_score *)
    61          (* meta_label *)
    "witness_v6_061"%string.
