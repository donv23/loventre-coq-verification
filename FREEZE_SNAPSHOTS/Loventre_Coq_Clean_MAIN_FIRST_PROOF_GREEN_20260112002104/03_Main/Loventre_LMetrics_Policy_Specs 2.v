From Stdlib Require Import Reals.
From Loventre_Geometry Require Import
  Loventre_LMetrics_JSON_Witness
  Loventre_LMetrics_Existence_Summary
  Loventre_LMetrics_Phase_Predicates
  Loventre_LMetrics_Policy_Spec.

Set Implicit Arguments.
Set Strict Implicit.
Unset Printing Implicit Defensive.

(** 
  Loventre_LMetrics_Policy_Specs.v

  Questo file sta in 03_Main e ha il ruolo di:
  - raccogliere in un unico punto il "nocciolo duro" esistenziale
    P-like vs NP_like-black-hole (espresso in termini di predicati su LMetrics),
  - collegarlo alle specifiche ideali di Policy formulate in Geometry,
  - introdurre una mini "Policy ideale astratta" (LMetrics -> GlobalColor * GlobalDecision)
    e dimostrare almeno una proprietà chiave (mai GC_green su black-hole).

  Importante: qui NON assumiamo che la Policy reale soddisfi queste
  specifiche; le consideriamo come obiettivi formali / modello ideale.
 *)

(** 1. Nocciolo duro esistenziale in forma predicativa *)

(* Ricordiamo lo statement del teorema (già provato in Loventre_LMetrics_Existence_Summary):

   Loventre_P_vs_NP_like_black_hole_exist_predicative :
     (exists m : LMetrics, is_P_like m)
     /\
     (exists m : LMetrics, is_NP_like_black_hole m).

   Qui ci interessa solo la PROPOSIZIONE:
   (exists m, is_P_like m) /\ (exists m, is_NP_like_black_hole m).
 *)

Definition Loventre_P_vs_NP_like_black_hole_Prop : Prop :=
  (exists m : LMetrics, is_P_like m)
  /\
  (exists m : LMetrics, is_NP_like_black_hole m).

(** 2. Richiamo della specifica ideale di Policy *)

(* Già definito in Loventre_LMetrics_Policy_Spec:

   policy_ideal_spec : Prop :=
     policy_never_green_on_black_hole_global /\
     policy_green_only_on_low_risk_non_black_hole_global /\
     policy_borderline_green_matches_P_like_accessible_global.
 *)

(** 3. Enunciato principale: nucleo P/NP_like-black-hole + spec ideale di Policy *)

Definition Loventre_Policy_Core_Program : Prop :=
  Loventre_P_vs_NP_like_black_hole_Prop
  /\
  policy_ideal_spec.

(** 
   Lettura informale:

   - Il pezzo [Loventre_P_vs_NP_like_black_hole_Prop] afferma
     che esistono configurazioni P-like non-black-hole e NP_like-black-hole
     nel senso dei predicati astratti su LMetrics (nocciolo duro).

   - Il pezzo [policy_ideal_spec] descrive come una Policy "ideale"
     dovrebbe colorare e decidere rispetto a tali configurazioni
     (mai GC_green su black-hole, GC_green solo su low risk non-black-hole,
     borderline green solo se P_like_accessible).

   In futuro, varianti di [Loventre_Policy_Core_Program] potranno essere:
   - assunte come obiettivo di progetto,
   - o scomposte in teoremi dimostrabili da una modellizzazione astratta
     della Policy (ad esempio una funzione ideale LMetrics -> (GlobalColor * GlobalDecision)).
 *)

(** 4. Mini Policy ideale astratta (solo colore + decisione "trasparente")

    Qui introduciamo una funzione astratta:

      ideal_policy_color    : LMetrics -> GlobalColor
      ideal_policy_decision : LMetrics -> GlobalDecision

    che rappresenta una Policy ideale su LMetrics, separata dai campi
    [loventre_global_color] e [loventre_global_decision] registrati dal motore.

    Per tenere il codice semplice e non dipendere da costruttori aggiuntivi
    di GlobalColor, introduciamo un colore "non-verde" astratto [GC_not_green]
    solo con la proprietà che è diverso da [GC_green].
 *)

Axiom GC_not_green : GlobalColor.
Axiom GC_not_green_neq_GC_green : GC_not_green <> GC_green.

(** Definiamo il colore ideale in funzione dell'orizzonte:

    - se [horizon_flag m = true] (black-hole), allora usiamo un colore
      non-verde [GC_not_green];

    - se [horizon_flag m = false] (non black-hole), allora usiamo [GC_green].

    Questa scelta garantisce già la proprietà "mai GC_green su black-hole".
 *)

Definition ideal_policy_color (m : LMetrics) : GlobalColor :=
  if horizon_flag m then GC_not_green else GC_green.

(** Per la decisione ideale, in questa prima versione astratta restiamo
    "trasparenti": non imponiamo nulla e riutilizziamo per ora il campo
    [loventre_global_decision m]. In futuro si potrà raffinare questa parte.
 *)

Definition ideal_policy_decision (m : LMetrics) : GlobalDecision :=
  loventre_global_decision m.

(** 4.1. Proprietà dimostrata: la Policy ideale non colora mai di GC_green
        una configurazione black-hole.

    Questa è l'analogo, per la Policy ideale, di:

      policy_never_green_on_black_hole_pointwise m :=
        is_black_hole m -> loventre_global_color m <> GC_green.

    Qui però usiamo [ideal_policy_color] al posto di [loventre_global_color].
 *)

Theorem ideal_policy_never_green_on_black_hole :
  forall m : LMetrics,
    is_black_hole m -> ideal_policy_color m <> GC_green.
Proof.
  intros m Hb.
  unfold is_black_hole in Hb.
  unfold ideal_policy_color.
  (* Sostituiamo [horizon_flag m] con [true] grazie a Hb *)
  rewrite Hb.
  simpl.
  intro Hc.
  (* In questo caso ideal_policy_color m = GC_not_green,
     quindi Hc afferma GC_not_green = GC_green,
     in contraddizione con GC_not_green_neq_GC_green. *)
  apply GC_not_green_neq_GC_green.
  exact Hc.
Qed.

(** 4.2. Osservazione (non dimostrata qui):

    Dalla definizione di [ideal_policy_color], si può anche ricavare
    una proprietà più debole ma utile:

      ideal_policy_color m = GC_green -> is_non_black_hole m.

    Ovvero: il colore verde ideale può emergere solo fuori dall'orizzonte.

    La parte "low risk" del secondo requisito di Policy, e il collegamento
    con [GD_borderline] e [is_P_like_accessible], richiederebbero invece
    di raffinare anche [ideal_policy_decision] in funzione di [risk_class]
    (e, se necessario, di altri campi di LMetrics).

    Per mantenere questo file pulito e senza [Admitted], in questa fase
    ci limitiamo alla proprietà chiave "mai GC_green su black-hole",
    che è completamente dimostrata per la mini Policy ideale.
 *)

