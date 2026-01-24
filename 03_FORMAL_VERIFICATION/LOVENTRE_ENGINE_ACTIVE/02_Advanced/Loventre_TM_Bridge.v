(** Loventre_TM_Bridge.v
    Bridge tra l'interfaccia astratta TM del Kernel
    e il modello concreto Loventre_TM_Base (modello eseguibile). *)

From Coq Require Import Arith List Bool.
Import ListNotations.

Require Import Loventre_Kernel Loventre_TM_Base.

Module Loventre_TM_Bridge.

  (** Moduli alias per chiarezza. *)
  Module Geo    := Loventre_Kernel.Loventre_Geometry.
  Module TMInt  := Loventre_Kernel.Loventre_TM_Interface.
  Module Corr   := Loventre_Kernel.Loventre_Correspondence.
  Module TMBase := Loventre_TM_Base.Loventre_TM_Base.

  (** ========================================================== *)
  (** 1. Isomorfismo Config astratta / Config concreta           *)
  (** ========================================================== *)

  Parameter cfg_to_concrete : TMInt.Config -> TMBase.Config.
  Parameter cfg_of_concrete : TMBase.Config -> TMInt.Config.

  Axiom cfg_roundtrip_abstract :
    forall c : TMInt.Config,
      cfg_of_concrete (cfg_to_concrete c) = c.

  Axiom cfg_roundtrip_concrete :
    forall c : TMBase.Config,
      cfg_to_concrete (cfg_of_concrete c) = c.

  (** ========================================================== *)
  (** 2. Compatibilità dell'evoluzione (next / TM_step)          *)
  (** ========================================================== *)

  Axiom next_compatible :
    forall c : TMInt.Config,
      cfg_to_concrete (TMInt.next c)
      = TMBase.next (cfg_to_concrete c).

  Axiom TM_step_compatible :
    forall (n : nat) (c : TMInt.Config),
      cfg_to_concrete (TMInt.TM_step n c)
      = TMBase.TM_step n (cfg_to_concrete c).

  (** ========================================================== *)
  (** 3. Compatibilità dei predicati overflow / stable / compl.  *)
  (** ========================================================== *)

  Axiom overflow_compatible :
    forall c : TMInt.Config,
      TMInt.overflow c <->
      TMBase.overflow (cfg_to_concrete c).

  Axiom stable_conf_compatible :
    forall c : TMInt.Config,
      TMInt.stable_conf c <->
      TMBase.stable_conf (cfg_to_concrete c).

  Axiom complexity_conf_compatible :
    forall c : TMInt.Config,
      TMInt.complexity_conf c =
      TMBase.complexity_conf (cfg_to_concrete c).

  (** ========================================================== *)
  (** 4. Compatibilità della polinomialità (polytime_config)     *)
  (** ========================================================== *)

  (* Nel Kernel, Corr.polytime_config è un predicato astratto su
     configurazioni TMInt.Config.

     In TM_Base, TMBase.polytime_config è una definizione concreta
     basata su accepts_in e su un polinomio di grado <= 3. *)
  Axiom polytime_config_compatible :
    forall c : TMInt.Config,
      Corr.polytime_config c <->
      TMBase.polytime_config (cfg_to_concrete c).

  (** ========================================================== *)
  (** 5. Embedding geometrico per configurazioni concrete        *)
  (** ========================================================== *)

  (** Per una configurazione concreta di TM_Base, usiamo:
        - cfg_of_concrete : TMBase.Config -> TMInt.Config
        - Corr.embed      : TMInt.Config -> Geo.M
      per ottenere un embedding nel mondo geometrico. *)
  Definition embed_concrete (c : TMBase.Config) : Geo.M :=
    Corr.embed (cfg_of_concrete c).

  (** ========================================================== *)
  (** 6. Lemmi ponte: TM polinomiale <-> geometria               *)
  (** ========================================================== *)

  (** Configurazione concreta polinomiale => punto contrattibile. *)
  Theorem concrete_polytime_implies_contractible :
    forall c : TMBase.Config,
      TMBase.polytime_config c ->
      Geo.contractible (embed_concrete c).
  Proof.
    intros c Hpoly_conc.
    set (c_abs := cfg_of_concrete c).

    (* Step 1: portiamo la polinomialità da TMBase a Corr.polytime_config. *)
    assert (Corr.polytime_config c_abs) as Hpoly_abs.
    { destruct (polytime_config_compatible c_abs)
        as [H_abs_to_conc H_conc_to_abs].
      (* H_abs_to_conc  : Corr.polytime_config c_abs
                          -> TMBase.polytime_config (cfg_to_concrete c_abs)
         H_conc_to_abs  : TMBase.polytime_config (cfg_to_concrete c_abs)
                          -> Corr.polytime_config c_abs *)
      apply H_conc_to_abs.
      unfold c_abs.
      rewrite cfg_roundtrip_concrete.
      exact Hpoly_conc. }

    (* Step 2: usiamo contractible_iff_polytime del Kernel. *)
    specialize (Corr.contractible_iff_polytime c_abs) as Hiff.
    destruct Hiff as [Hpoly_to_contr Hcontr_to_poly].
    apply Hpoly_to_contr in Hpoly_abs.

    (* Step 3: riconnettiamo con embed_concrete. *)
    unfold embed_concrete.
    unfold c_abs in Hpoly_abs.
    exact Hpoly_abs.
  Qed.

  (** Configurazione concreta non polinomiale => punto non contrattibile. *)
  Theorem concrete_nonpolytime_implies_noncontractible :
    forall c : TMBase.Config,
      ~ TMBase.polytime_config c ->
      Geo.non_contractible (embed_concrete c).
  Proof.
    intros c Hnonpoly_conc.
    set (c_abs := cfg_of_concrete c).

    (* Step 1: ricaviamo ~Corr.polytime_config c_abs. *)
    assert (~ Corr.polytime_config c_abs) as Hnonpoly_abs.
    { intros Hpoly_abs.
      destruct (polytime_config_compatible c_abs)
        as [H_abs_to_conc H_conc_to_abs].
      (* Da Hpoly_abs otteniamo TMBase.polytime_config (cfg_to_concrete c_abs). *)
      specialize (H_abs_to_conc Hpoly_abs).
      unfold c_abs in H_abs_to_conc.
      rewrite cfg_roundtrip_concrete in H_abs_to_conc.
      apply Hnonpoly_conc.
      exact H_abs_to_conc. }

    (* Step 2: usiamo divergent_iff_noncontractible del Kernel. *)
    specialize (Corr.divergent_iff_noncontractible c_abs) as Hiff.
    destruct Hiff as [Hnonpoly_to_noncontr Hnoncontr_to_nonpoly].
    apply Hnonpoly_to_noncontr in Hnonpoly_abs.

    (* Step 3: riconnettiamo con embed_concrete. *)
    unfold embed_concrete.
    unfold c_abs in Hnonpoly_abs.
    exact Hnonpoly_abs.
  Qed.

End Loventre_TM_Bridge.

