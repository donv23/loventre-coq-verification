(** 
  Loventre_JSON_Witness_Profile_Bridge_v3.v
  -----------------------------------------

  Layer Main v3 / v3+

  Ruolo di questo modulo (Super Seed v3/v3+):

  - Fornire una vista "JSON/profile" compatta del mini-teorema v3,
    espressa in termini delle classi Loventre

        In_P_Lov
        In_Pacc_Lov
        In_NP_bh_Lov

    senza entrare nei dettagli del bus fisico.

  - Questo modulo NON introduce nuovi witness: riusa semplicemente
    i lemma già dimostrati in

        Loventre_Class_Separation_v3

    che a loro volta si appoggiano sui witness JSON definiti in

        Loventre_LMetrics_JSON_Witness

    e sui lemma di

        Loventre_Witness_v3.

  - In questo modo evitiamo deliberatamente ogni clash tra il tipo
    astratto [LMetrics] di [Loventre_LMetrics_JSON_Witness] e il
    tipo fisico del bus [Loventre_Metrics_Bus.LMetrics]: qui
    restiamo solo al livello "logico/classi".

  ATTENZIONE:

  - File nel namespace [Loventre_Main].
  - Usa solo i prefissi:

        Loventre_Core
        Loventre_Geometry
        Loventre_Main

  - Niente [From Loventre_Advanced ...] nei file v3/v3+.
*)

From Stdlib Require Import Init.Logic.

From Loventre_Geometry Require Import
  Loventre_LMetrics_JSON_Witness.

From Loventre_Main Require Import
  Loventre_Class_Separation_v3.

(** 
  1. Enunciati "profilo JSON" del mini-teorema
  --------------------------------------------

  Formuliamo due Prop compatte che rispecchiano esattamente il
  contenuto del mini-teorema v3, ma con un nome esplicito lato
  JSON/profile.
*)

Definition Loventre_JSON_P_vs_NPbh_Loventre_v3_exists_Prop : Prop :=
  exists m, In_NP_bh_Lov m /\ ~ In_Pacc_Lov m.

Definition Loventre_JSON_P_vs_NPbh_Loventre_v3_nonsubset_Prop : Prop :=
  ~ (forall m, In_NP_bh_Lov m -> In_Pacc_Lov m).

(** 
  2. Prove: riuso diretto dei lemma di Class_Separation_v3
  --------------------------------------------------------

  Utilizziamo i lemma già dimostrati in [Loventre_Class_Separation_v3]:

    - Loventre_exists_NPbh_not_Pacc_Lov_v3 :
        exists m, In_NP_bh_Lov m /\ ~ In_Pacc_Lov m.

    - Loventre_NPbh_not_subset_Pacc_Lov_v3 :
        ~ (forall m, In_NP_bh_Lov m -> In_Pacc_Lov m).

  In questo modo otteniamo enunciati "profilo JSON" senza dover
  nominare direttamente i witness m_NP_TSP, evitando clash di tipi
  tra LMetrics astratto e LMetrics del bus.
*)

Theorem Loventre_JSON_P_vs_NPbh_Loventre_v3_exists :
  Loventre_JSON_P_vs_NPbh_Loventre_v3_exists_Prop.
Proof.
  unfold Loventre_JSON_P_vs_NPbh_Loventre_v3_exists_Prop.
  exact Loventre_exists_NPbh_not_Pacc_Lov_v3.
Qed.

Theorem Loventre_JSON_P_vs_NPbh_Loventre_v3_nonsubset :
  Loventre_JSON_P_vs_NPbh_Loventre_v3_nonsubset_Prop.
Proof.
  unfold Loventre_JSON_P_vs_NPbh_Loventre_v3_nonsubset_Prop.
  exact Loventre_NPbh_not_subset_Pacc_Lov_v3.
Qed.

