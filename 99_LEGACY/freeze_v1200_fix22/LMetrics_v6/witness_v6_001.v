(** Loventre Engine — witness_v6_001
    Tab leggera v1200 — primo seed alternativo
    Conforme alle regole auree (Gennaio 2026)
 *)

From Stdlib Require Import Reals.
From Stdlib Require Import String.
From LMetrics_v6 Require Import LMetrics_v6_types.

(* Witness 001: valori placeholder diversi dal minimale *)
Definition witness_v6_001_example : LMetrics :=
  mkLMetrics
    0.1%R      (* kappa_eff *)
    0.2%R      (* entropy_eff *)
    1.0%R      (* mass_eff *)
    0.5%R      (* inertial_idx *)
    0.3%R      (* risk_index *)
    MEDIUM     (* risk_class *)
    SAFE       (* loventre_global_decision *)
    YELLOW     (* loventre_global_color *)
    0.4%R      (* loventre_global_score *)
    1          (* meta_label *)
    "witness_v6_001"%string.   (* source_file *)

