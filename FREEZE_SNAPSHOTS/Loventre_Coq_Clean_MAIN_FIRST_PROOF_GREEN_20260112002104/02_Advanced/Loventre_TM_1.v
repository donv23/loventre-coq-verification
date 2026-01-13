(** Loventre_TM_1.v
    Primo esempio di macchina di Turing per il progetto Loventre,
    allineato al modello Loventre_TM_Base e collegato alla geometria
    tramite il bridge. *)

From Stdlib Require Import Arith List Bool.
Import ListNotations.

Require Import Loventre_TM_Base Loventre_TM_Bridge Loventre_Kernel.

Module Loventre_TM_1.

  (** Alias per i moduli che useremo. *)
  Module TMBase := Loventre_TM_Base.Loventre_TM_Base.
  Module Bridge := Loventre_TM_Bridge.Loventre_TM_Bridge.
  Module Geo    := Loventre_Kernel.Loventre_Geometry.

  (** Configurazione iniziale astratta della TM_1.

      In questa fase non fissiamo ancora il dettaglio di:
      - TMBase.Symbol
      - TMBase.TM_State
      - TMBase.Transition
      - TMBase.input_of_word

      Tutto ciò resta parametrico nel modello di base; qui lavoriamo
      solo con una configurazione iniziale tm1_init. *)
  Parameter tm1_init : TMBase.Config.

  (** Esecuzione di TM_1 per n passi, a partire da tm1_init. *)
  Definition tm1_step (n : nat) : TMBase.Config :=
    TMBase.TM_step n tm1_init.

  (** Linguaggio accettato da TM_1 in tempo t su una parola w. *)
  Definition tm1_accepts_in (w : TMBase.Word) (t : nat) : bool :=
    TMBase.accepts_in tm1_init w t.

  (** Ipotesi di polinomialità per TM_1 nel senso TMBase.polytime_config. *)
  Axiom tm1_polytime :
    TMBase.polytime_config tm1_init.

  (** Punto geometrico associato alla configurazione iniziale tm1_init.

      Usiamo embed_concrete del bridge, che combina:
      - cfg_of_concrete : TMBase.Config -> TM_Interface.Config
      - Corr.embed      : TM_Interface.Config -> Geo.M *)
  Definition tm1_geom_point : Geo.M :=
    Bridge.embed_concrete tm1_init.

  (** Lemma ponte: TM_1 polinomiale => punto geometrico contrattibile. *)
  Theorem tm1_geom_contractible :
    Geo.contractible tm1_geom_point.
  Proof.
    unfold tm1_geom_point.
    apply Bridge.concrete_polytime_implies_contractible.
    exact tm1_polytime.
  Qed.

End Loventre_TM_1.

