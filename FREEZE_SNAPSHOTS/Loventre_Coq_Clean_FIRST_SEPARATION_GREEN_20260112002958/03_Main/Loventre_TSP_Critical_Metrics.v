(** Loventre_TSP_Critical_Metrics.v
    Versione metrica (LMetrics) della famiglia TSP_crit.

    Collegamento concettuale:
      - Loventre_TSP_Critical_Family.v:
          TSP_crit_family : Conj.family (istanze astratte di problema TSP-like).
      - Loventre_Metrics_Bus.v:
          LMetrics, meta_label, global_decision, ecc.

    Qui introduciamo:
      - TSP_crit_metrics_family : nat -> LMetrics,
        che rappresenta la "traiettoria metrica" delle istanze TSP_crit_n.
      - ipotesi strutturate sulla meta_label (NP-like critica / black hole).
 *)

From Stdlib Require Import Arith Reals.

Require Import Loventre_Conjecture.
Require Import Loventre_TSP_Critical_Family.
Require Import Loventre_Metrics_Bus.

Open Scope R_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Loventre_TSP_Critical_Metrics.

  Module Conj    := Loventre_Conjecture.Loventre_Conjecture.
  Module TSPCrit := Loventre_TSP_Critical_Family.Loventre_TSP_Critical_Family.
  Module MB      := Loventre_Metrics_Bus.Loventre_Metrics_Bus.

  (* ----------------------------------------------------------- *)
  (* 1. Famiglia metrica TSP_crit_metrics_family                 *)
  (* ----------------------------------------------------------- *)

  (** Per ogni n, TSP_crit_metrics_family n è lo stato LMetrics
      associato all'istanza TSP_crit_n del livello "Conjecture".
      In questa fase lo lasciamo come [Parameter] astratto. *)

  Parameter TSP_crit_metrics_family : nat -> MB.LMetrics.

  (* ----------------------------------------------------------- *)
  (* 2. Allineamento concettuale NP-like critico / meta_label    *)
  (* ----------------------------------------------------------- *)

  (** Ipotesi: la famiglia TSP_crit è NP-like critica (lato
      Loventre_Conjecture) e questa natura si riflette nel livello
      metrico attraverso la meta_label.

      Versione minimale:
        - per ogni n, la meta_label è NP_like_critico oppure
          NP_like_black_hole.
      Una versione più fine (in futuro) potrà usare una soglia n0
      e un epsilon sul global_score, come nello schema di
      "Loventre_crit_family_collapse" della nota. *)

  Axiom TSP_crit_metrics_family_is_NP_like_critical :
    forall n : nat,
      MB.meta_label (TSP_crit_metrics_family n) = MB.NP_like_critico \/
      MB.meta_label (TSP_crit_metrics_family n) = MB.NP_like_black_hole.

  (** Opzionalmente si potrebbero aggiungere assiomi su:
        - crescita di V0, a_min, mass_eff, inertial_idx,
        - comportamento di p_tunnel e P_success,
        - relazione tra risk_index / risk_class e global_decision.
      Per questa fase li teniamo aperti, in attesa della versione
      stabilizzata del motore Python. *)

End Loventre_TSP_Critical_Metrics.

