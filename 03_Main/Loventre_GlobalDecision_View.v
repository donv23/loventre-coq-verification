(* Loventre_GlobalDecision_View.v
   Seed (dicembre 2025) per la vista Coq delle decisioni globali
   del Loventre Policy Bridge.
*)

From Coq Require Import Bool.

Require Import Loventre_Metrics_Bus.

Module MB := Loventre_Metrics_Bus.

(* Alias per lo stato del bus di metriche. *)
Definition BusState : Type := MB.LMetrics.

(* Tipo di decisione globale, in parallelo con il DecisionLabel Python. *)
Inductive GlobalDecision : Type :=
| Dec_Unknown
| Dec_Allow
| Dec_Warn
| Dec_Block
| Dec_Investigate
.

(* Predicati "di vista" sulle decisioni. *)

Definition Decision_is_unknown (d : GlobalDecision) : Prop :=
  match d with
  | Dec_Unknown => True
  | _ => False
  end.

Definition Decision_is_allow_like (d : GlobalDecision) : Prop :=
  match d with
  | Dec_Allow => True
  | _ => False
  end.

Definition Decision_is_warn_like (d : GlobalDecision) : Prop :=
  match d with
  | Dec_Warn => True
  | _ => False
  end.

Definition Decision_is_block_like (d : GlobalDecision) : Prop :=
  match d with
  | Dec_Block => True
  | _ => False
  end.

Definition Decision_is_investigate_like (d : GlobalDecision) : Prop :=
  match d with
  | Dec_Investigate => True
  | _ => False
  end.

(* Policy Bridge astratto:
   lato Python e' decide_from_metrics : bus -> GlobalDecision;
   qui lo modelliamo come funzione pura LMetrics -> GlobalDecision.
*)

Parameter PolicyBridge : BusState -> GlobalDecision.

(* Regimi di rischio astratti.

   Questi predicati riassumono tutta la fisica-informazionale:
   - High_risk_regime m    ~ "risk_class = high/critical" o simili;
   - Medium_risk_regime m  ~ "risk_class = medium/elevated";
   - Low_risk_regime m     ~ "risk_class = low", lontano dall'orizzonte.
*)

Parameter High_risk_regime   : BusState -> Prop.
Parameter Medium_risk_regime : BusState -> Prop.
Parameter Low_risk_regime    : BusState -> Prop.

(* Assiomi qualitativi coerenti con la logica Python:

   - alto rischio  -> la decisione e' block-like;
   - rischio medio -> la decisione e' warn-like;
   - rischio basso -> la decisione e' allow-like.
*)

Axiom PolicyBridge_block_high_risk :
  forall m : BusState,
    High_risk_regime m ->
    Decision_is_block_like (PolicyBridge m).

Axiom PolicyBridge_warn_medium_risk :
  forall m : BusState,
    Medium_risk_regime m ->
    Decision_is_warn_like (PolicyBridge m).

Axiom PolicyBridge_allow_low_risk :
  forall m : BusState,
    Low_risk_regime m ->
    Decision_is_allow_like (PolicyBridge m).

