(**
  Loventre_LMetrics_Phase_CANON.v

  Predicati di fase CANON
  Versione SAFE, non invasiva
  Basata esclusivamente su LMetrics v5.0

  Questo file è SHADOW:
  - non è importato da nessun modulo
  - non entra nel makefile
  - non rompe il grafo esistente

  Dicembre 2025
*)

From Stdlib Require Import Reals.Rdefinitions Reals.Raxioms.

From Loventre_Advanced.Geometry Require Import
  Loventre_LMetrics_Structure.

(* ===================================================== *)
(* === Predicati di fase CANON (soft semantics)       === *)
(* ===================================================== *)

Module Loventre_LMetrics_Phase_CANON.

  (* SAFE: buon tunneling e buona probabilità di successo *)
  Definition is_SAFE (m : LMetrics) : Prop :=
    (0.5 <= m.(p_tunnel))%R /\ (0.5 <= m.(P_success))%R.

  (* BLACKHOLE: tunneling scarso e successo basso *)
  Definition is_BLACKHOLE (m : LMetrics) : Prop :=
    (m.(p_tunnel) < 0.3)%R /\ (m.(P_success) < 0.5)%R.

  (* WARNING: zona intermedia *)
  Definition is_WARNING (m : LMetrics) : Prop :=
    ~ is_SAFE m /\ ~ is_BLACKHOLE m.

End Loventre_LMetrics_Phase_CANON.

