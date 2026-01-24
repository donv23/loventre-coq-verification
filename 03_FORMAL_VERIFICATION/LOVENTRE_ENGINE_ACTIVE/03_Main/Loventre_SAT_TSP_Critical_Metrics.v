(** * Loventre_SAT_TSP_Critical_Metrics
    Predicati di criticità SAT/TSP sul bus di metriche Loventre.
 *)

Require Import Loventre_Metrics_Bus.

(** Alias per lo stato del bus di metriche. *)
Definition BusState : Type := Loventre_Metrics_Bus.LMetrics.

(** Classe di rischio "alta" astratta sul bus. *)
Parameter High_risk_class : Loventre_Metrics_Bus.RiskClass.

(** Predicati di criticità:
    per ora SAT_crit e TSP_crit coincidono con la stessa high risk class.
 *)

Definition SAT_crit (m : BusState) : Prop :=
  Loventre_Metrics_Bus.risk_class m = High_risk_class.

Definition TSP_crit (m : BusState) : Prop :=
  Loventre_Metrics_Bus.risk_class m = High_risk_class.

(** Predicato "witness metrico" per il teorema:
    uno stato metrico è witness se è SAT-critico o TSP-critico.
 *)

Definition Metrics_witness (m : BusState) : Prop :=
  SAT_crit m \/ TSP_crit m.

(** Lemmi base: criticità SAT/TSP implica essere un witness metrico. *)

Lemma SAT_crit_implies_Metrics_witness :
  forall m : BusState, SAT_crit m -> Metrics_witness m.
Proof.
  intros m Hsat.
  left; exact Hsat.
Qed.

Lemma TSP_crit_implies_Metrics_witness :
  forall m : BusState, TSP_crit m -> Metrics_witness m.
Proof.
  intros m Htsp.
  right; exact Htsp.
Qed.

(** ------------------------------------------------------------ *)
(**  Sezione: relazioni qualitative astratte sul bus di metriche  *)
(** ------------------------------------------------------------ *)

(** Predicati qualitativi astratti legati ad alcuni campi di LMetrics.
    Non fissiamo qui nessun dettaglio numerico (soglie, formule, ecc.):
    sono semplici proprietà logiche su BusState.
 *)

Parameter High_risk_index : BusState -> Prop.
Parameter Near_horizon : BusState -> Prop.
Parameter High_tunneling_probability : BusState -> Prop.

(** Axioms: criticità SAT/TSP implica certe proprietà qualitative
    del bus (alto rischio, vicinanza all'orizzonte, tunneling elevato, ecc.).
    Queste sono ipotesi dichiarate in modo trasparente, che in futuro
    potranno essere rese più precise o derivate da una geometria
    formalizzata.
 *)

Axiom SAT_crit_implies_High_risk_index :
  forall m : BusState, SAT_crit m -> High_risk_index m.

Axiom SAT_crit_implies_Near_horizon_or_High_tunneling :
  forall m : BusState, SAT_crit m -> Near_horizon m \/ High_tunneling_probability m.

Axiom TSP_crit_implies_High_risk_index :
  forall m : BusState, TSP_crit m -> High_risk_index m.

Axiom TSP_crit_implies_Near_horizon_or_High_tunneling :
  forall m : BusState, TSP_crit m -> Near_horizon m \/ High_tunneling_probability m.

