(** Loventre_Metrics_Bus.v
    Versione Coq minimale del Loventre Metrics Bus (LMetrics).

    Basato sulla nota:
      "LOVENTRE METRICS BUS NOTA PER FORMALIZZAZIONE COQ" (dicembre 2025).

    Scopo:
      - Definire i tipi enumerativi fondamentali:
          * TimeRegime, MetaLabel, GlobalDecision, GlobalColor, RiskClass.
      - Definire il record LMetrics con i campi fisico-informazionali.
      - Lasciare astratte (come [Parameter]) le funzioni derivate:
          * meta_label, global_decision, global_color, global_score.
 *)

From Coq Require Import Reals Bool.

Open Scope R_scope.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Loventre_Metrics_Bus.

  (* ----------------------------------------------------------- *)
  (* 1. Tipi enumerativi fondamentali                            *)
  (* ----------------------------------------------------------- *)

  (** Regime temporale: corrisponde al "time_regime" del bus Python. *)
  Inductive TimeRegime :=
  | time_euclidean
  | time_threshold
  | time_hyperbolic.

  (** Meta label di complessità globale. *)
  Inductive MetaLabel :=
  | P_like_accessibile
  | quasi_critico_Loventre
  | NP_like_critico
  | NP_like_black_hole
  | zona_intermedia.

  (** Decisione globale (policy bridge astratto). *)
  Inductive GlobalDecision :=
  | INSISTI
  | VALUTA
  | RITIRA.

  (** Colore globale, principalmente per presentazione. *)
  Inductive GlobalColor :=
  | GREEN
  | AMBER
  | RED.

  (** Classe di rischio aggregata. *)
  Inductive RiskClass :=
  | RISK_LOW
  | RISK_MEDIUM
  | RISK_HIGH
  | RISK_BLACK_HOLE.

  (* ----------------------------------------------------------- *)
  (* 2. Record LMetrics (bus fisico-informazionale minimale)     *)
  (* ----------------------------------------------------------- *)

  Record LMetrics := {
    (* Curvatura / entropia / barriera *)
    kappa_eff     : R;        (* curvatura informazionale efficace *)
    entropy_eff   : R;        (* entropia informazionale efficace  *)
    V0            : R;        (* altezza barriera                  *)
    a_min         : R;        (* spessore minimo barriera          *)

    (* Tunneling e successo *)
    p_tunnel      : R;        (* probabilità di tunneling per tentativo *)
    P_success     : R;        (* probabilità di successo entro N_budget *)

    (* Regime temporale *)
    gamma_dilation : R;       (* fattore di dilatazione temporale interno *)
    time_regime    : TimeRegime;

    (* Massa / inerzia Loventre *)
    mass_eff      : R;        (* massa informazionale effettiva           *)
    inertial_idx  : R;        (* indice di difficoltà inerziale           *)

    (* Rischio aggregato Einstein–Loventre *)
    risk_index    : R;        (* indice aggregato di rischio              *)
    risk_class    : RiskClass;

    (* Dati relativistici compatti per estensioni Schwarzschild/Hawking *)
    chi_compactness : R;      (* parametro di compattezza                 *)
    horizon_flag    : bool    (* True se near_horizon / supercritical     *)
  }.

  (* ----------------------------------------------------------- *)
  (* 3. Funzioni derivate (MetaLabel, decisione, colore, score)  *)
  (* ----------------------------------------------------------- *)

  (** In questa fase le teniamo astratte come [Parameter].
      In futuro potranno essere definite a partire dai campi primitivi
      (kappa_eff, V0, risk_index, ecc.). *)

  Parameter meta_label      : LMetrics -> MetaLabel.
  Parameter global_decision : LMetrics -> GlobalDecision.
  Parameter global_color    : LMetrics -> GlobalColor.
  Parameter global_score    : LMetrics -> R.

End Loventre_Metrics_Bus.

