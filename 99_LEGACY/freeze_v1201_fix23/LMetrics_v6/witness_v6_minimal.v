(** Loventre Engine — witness_v6_minimal
    Tab leggera v1200 — compilazione di base
    Conforme alle regole auree (Gennaio 2026)
 *)

From Stdlib Require Import Reals.
From Stdlib Require Import String.
From LMetrics_v6 Require Import LMetrics_v6_types.

(* Witness minimale conforme al record reale LMetrics *)
Definition witness_v6_minimal_example : LMetrics :=
  mkLMetrics
    0%R      (* kappa_eff *)
    0%R      (* entropy_eff *)
    0%R      (* mass_eff *)
    0%R      (* inertial_idx *)
    0%R      (* risk_index *)
    LOW      (* risk_class *)
    SAFE     (* loventre_global_decision *)
    GREEN    (* loventre_global_color *)
    0%R      (* loventre_global_score *)
    0        (* meta_label *)
    ""%string.  (* source_file *)

