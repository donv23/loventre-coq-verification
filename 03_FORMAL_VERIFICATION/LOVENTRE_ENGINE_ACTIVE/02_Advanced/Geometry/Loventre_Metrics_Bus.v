(** * Loventre_Metrics_Bus.v
    Bus di metriche tipato per il Loventre Engine
    Stato: seed 2025-12 (allineato al motore Python)

    Questo modulo definisce:

    - TimeRegime        : regimi temporali (euclideo / soglia / iperbolico);
    - RiskClass         : classi di rischio (P-like / NP-like critico / black-hole);
    - MetaLabel         : etichette meta (P_like_like, NP_like_critico, ...);
    - GlobalDecision    : decisione qualitativa globale (safe/borderline/critical/invalid);
    - GlobalColor       : codifica a colori GREEN/AMBER/RED/UNKNOWN;
    - LMetrics          : record che raccoglie il "Loventre Metrics Bus" tipato,
                          incluse le informazioni di Global Decision.

    L'obiettivo è avere una controparte formale del bus Python
    (metrics: dict) usato dal Loventre Engine, senza fissare qui
    alcun dettaglio numerico dell'algoritmo.
 *)

From Coq Require Import Reals.
From Coq Require Import Bool.Bool.

Open Scope R_scope.

(** ** Regimi temporali *)

Inductive TimeRegime :=
  | time_euclidean   (* regime "piatto" / subcritico *)
  | time_threshold   (* regime di soglia / transizione *)
  | time_hyperbolic. (* regime fortemente curvo / iperbolico *)



(** ** Classi di rischio *)

Inductive RiskClass :=
  | risk_low                 (* P-like / subcritico *)
  | risk_medium              (* precritico / misto *)
  | risk_np_like_critico     (* NP_like-critico (zona near-horizon) *)
  | risk_np_like_black_hole  (* NP_like "buco nero" *)
  | risk_unknown.            (* fallback / non classificato *)



(** ** MetaLabel (label meta-informazionale di famiglia/istanza)

    Queste etichette sono pensate per allinearsi con le label Python:

      - "P_like_like"
      - "NP_like_critico"
      - "NP_like_black_hole"
      - "unknown"
 *)

Inductive MetaLabel :=
  | meta_P_like_like
  | meta_NP_like_critico
  | meta_NP_like_black_hole
  | meta_unknown.



(** ** GlobalDecision (vista concettuale)

    Lato Python, il Policy Bridge produce etichette stringa stabili:

      "safe" | "borderline" | "critical" | "invalid"

    Qui le rappresentiamo come costruttori di un tipo induttivo astratto.
 *)

Inductive GlobalDecision :=
  | GD_safe
  | GD_borderline
  | GD_critical
  | GD_invalid.



(** ** GlobalColor (codifica a colori della decisione operativa)

    Collegato al livello operativo INSISTI / VALUTA / RITIRA:

      - GREEN  ~ INSISTI / regime favorevole;
      - AMBER  ~ VALUTA / regime borderline;
      - RED    ~ RITIRA / regime critico;
      - UNKNOWN per casi non classificati / invalido.
 *)

Inductive GlobalColor :=
  | GC_green
  | GC_amber
  | GC_red
  | GC_unknown.



(** ** Record LMetrics

    Questo è il "Loventre Metrics Bus" tipato. I campi sono pensati
    per corrispondere (a livello concettuale) alle chiavi del dict
    metrics del motore Python:

      - kappa_eff        ~ "kappa_eff"
      - entropy_eff      ~ "entropy_eff"
      - V0               ~ "V0"
      - a_min            ~ "a_min"
      - p_tunnel         ~ "p_tunnel"
      - P_success        ~ "P_success"
      - gamma_dilation   ~ "gamma_dilation" / "gamma_schw"
      - time_regime      ~ "time_regime"
      - mass_eff         ~ "mass_eff"
      - inertial_idx     ~ "inertial_idx"
      - risk_index       ~ "risk_index"
      - risk_class       ~ "risk_class"
      - meta_label       ~ "meta_label"
      - chi_compactness  ~ "chi_compactness"
      - horizon_flag     ~ "horizon_flag"

    In aggiunta, includiamo il blocco di Global Decision:

      - loventre_global_decision : GlobalDecision
      - loventre_global_color    : GlobalColor
      - loventre_global_score    : R

    che corrispondono concettualmente alle chiavi Python:

      - "global_decision_label"   (safe/borderline/critical/invalid)
      - "loventre_global.global_color" (GREEN/AMBER/RED)
      - "loventre_global.global_score" (scala [0,1] che collassa in regime critico)
 *)

Record LMetrics := {
  kappa_eff : R;
  entropy_eff : R;
  V0 : R;
  a_min : R;

  p_tunnel : R;
  P_success : R;

  gamma_dilation : R;
  time_regime : TimeRegime;

  mass_eff : R;
  inertial_idx : R;

  risk_index : R;
  risk_class : RiskClass;

  meta_label : MetaLabel;

  chi_compactness : R;
  horizon_flag : bool;

  loventre_global_decision : GlobalDecision;
  loventre_global_color : GlobalColor;
  loventre_global_score : R
}.



(** ** Predicati di utilità (bozza)

    Questi predicati non fissano ancora le soglie numeriche precise:
    esprimono solo la struttura logica P-like / NP-like critica / black-hole.
 *)

Definition is_subcritical (m : LMetrics) : Prop :=
  risk_class m = risk_low.

Definition is_precritical_or_mixed (m : LMetrics) : Prop :=
  risk_class m = risk_medium.

Definition is_np_like_critical (m : LMetrics) : Prop :=
  risk_class m = risk_np_like_critico.

Definition is_black_hole_like (m : LMetrics) : Prop :=
  risk_class m = risk_np_like_black_hole.

Definition is_near_horizon (m : LMetrics) : Prop :=
  horizon_flag m = true.

Definition is_globally_safe (m : LMetrics) : Prop :=
  loventre_global_decision m = GD_safe.

Definition is_globally_critical (m : LMetrics) : Prop :=
  loventre_global_decision m = GD_critical.

Definition is_globally_invalid (m : LMetrics) : Prop :=
  loventre_global_decision m = GD_invalid.


