(** Loventre_SAT_Critical_Metrics.v
    Versione metrica (LMetrics) della famiglia SAT_crit.

    Collegamento concettuale:
      - Loventre_SAT_Critical_Family.v:
          SAT_crit_family : Conj.family (istanze astratte SAT-like critiche).
      - Loventre_Metrics_Bus.v:
          LMetrics, meta_label, global_decision, ecc.

    Qui introduciamo:
      - SAT_crit_metrics_family : nat -> LMetrics,
        che rappresenta la "traiettoria metrica" delle istanze SAT_crit_n.
      - ipotesi strutturata sulla meta_label:
          per ogni n, il regime è NP_like_critico.
 *)

From Stdlib Require Import Arith Reals.

Require Import Loventre_Conjecture.
Require Import Loventre_SAT_Critical_Family.
Require Import Loventre_Metrics_Bus.

Open Scope R_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Loventre_SAT_Critical_Metrics.

  Module Conj    := Loventre_Conjecture.Loventre_Conjecture.
  Module SATCrit := Loventre_SAT_Critical_Family.Loventre_SAT_Critical_Family.
  Module MB      := Loventre_Metrics_Bus.Loventre_Metrics_Bus.

  (* ----------------------------------------------------------- *)
  (* 1. Famiglia metrica SAT_crit_metrics_family                 *)
  (* ----------------------------------------------------------- *)

  Parameter SAT_crit_metrics_family : nat -> MB.LMetrics.

  (* ----------------------------------------------------------- *)
  (* 2. Allineamento concettuale NP-like critico / meta_label    *)
  (* ----------------------------------------------------------- *)

  Axiom SAT_crit_metrics_family_is_NP_like_critical :
    forall n : nat,
      MB.meta_label (SAT_crit_metrics_family n) = MB.NP_like_critico.

End Loventre_SAT_Critical_Metrics.

