From Stdlib Require Import List String.
Import ListNotations.

Require Import Loventre_LMetrics_JSON_Link.

(**
  Loventre_LMetrics_SAFE_Tags_v3

  Scopo (v3):
  - introdurre tre tag logici astratti su LMetrics_JSON_Link:
      is_SAFE, is_ACCESSIBLE, is_BLACKHOLE;
  - fornire un lemma di copertura molto debole
      Loventre_SAFE_ACCESSIBLE_bridge :
        forall lm, is_SAFE lm \/ is_ACCESSIBLE lm \/ is_BLACKHOLE lm.

  Nota importante:
  - in questa versione v3 le tre definizioni sono PLACEHOLDER (tutte True);
  - la semantica reale verrà raffinata in v4/v5 quando
    agganceremo in modo più stretto risk_class / meta_label
    al bus fisico-informazionale del motore Python.
*)

Definition is_SAFE (lm : LMetrics_JSON_Link) : Prop :=
  True.

Definition is_ACCESSIBLE (lm : LMetrics_JSON_Link) : Prop :=
  True.

Definition is_BLACKHOLE (lm : LMetrics_JSON_Link) : Prop :=
  True.

Lemma Loventre_SAFE_ACCESSIBLE_bridge :
  forall lm, is_SAFE lm \/ is_ACCESSIBLE lm \/ is_BLACKHOLE lm.
Proof.
  intros lm.
  left.
  unfold is_SAFE.
  exact I.
Qed.

