(** Loventre_Kernel.v
    Kernel astratto per il Teorema di Loventre (versione pulita). *)

From Stdlib Require Import Arith ZArith Lia.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* ================================================================ *)
(** * Modulo geometrico astratto                                    *)
(* ================================================================ *)

Module Loventre_Geometry.

  Parameter M : Type.

  Parameter Complexity : M -> nat.
  Parameter g          : M -> M -> nat.
  Parameter kappa      : M -> Z.
  Parameter alpha_c    : Z.
  Parameter Flow       : nat -> M -> M.
  Parameter base_point : M.

  (** Sottocritico / supercritico secondo la soglia di curvatura alpha_c *)

  Definition subcritical (x : M) : Prop :=
    (kappa x < alpha_c)%Z.

  Definition supercritical (x : M) : Prop :=
    (kappa x >= alpha_c)%Z.

  (** Stabilità dinamica: dopo un certo N il flusso non cambia più. *)

  Definition stable (x : M) : Prop :=
    exists N : nat, forall n : nat,
      (n >= N)%nat -> Flow n x = Flow N x.

  (** Divergenza dinamica: continua a “uscire” da qualunque N. *)

  Definition divergent (x : M) : Prop :=
    forall N : nat, exists n : nat,
      (n >= N)%nat /\ Flow n x <> Flow N x.

  (** Contrattibile / non contrattibile sono lasciati come predicati astratti,
      ma collegati alla dinamica tramite assiomi strutturali. *)

  Parameter contractible      : M -> Prop.
  Parameter non_contractible  : M -> Prop.

  Axiom contractible_exclusive :
    forall x : M, contractible x -> ~ non_contractible x.

  Axiom non_contractible_exclusive :
    forall x : M, non_contractible x -> ~ contractible x.

End Loventre_Geometry.

(* ================================================================ *)
(** * Interfaccia astratta per le macchine di Turing                *)
(* ================================================================ *)

Module Loventre_TM_Interface.

  Parameter Config  : Type.
  Parameter TMState : Type.

  (** Evoluzione di un singolo passo. *)
  Parameter next : Config -> Config.

  (** Overflow: la configurazione è “fuori scala” (memoria, tempo, …). *)
  Parameter overflow : Config -> Prop.

  (** Configurazione stabile: lo stato della TM non cambia più. *)
  Parameter stable_conf : Config -> Prop.

  (** Complessità locale (dimensione del nastro, ecc.). *)
  Parameter complexity_conf : Config -> nat.

  (** Evoluzione in n passi. *)
  Parameter TM_step : nat -> Config -> Config.

  Axiom TM_step_0 :
    forall c : Config, TM_step 0 c = c.

  Axiom TM_step_S :
    forall (n : nat) (c : Config),
      TM_step (S n) c = TM_step n (next c).

End Loventre_TM_Interface.

(* ================================================================ *)
(** * Corrispondenza geometria–TM                                   *)
(* ================================================================ *)

Module Loventre_Correspondence.

  Module Geo := Loventre_Geometry.
  Module TM  := Loventre_TM_Interface.

  (** Immersione delle configurazioni TM nello spazio geometrico. *)
  Parameter embed : TM.Config -> Geo.M.

  Axiom embed_injective :
    forall c1 c2 : TM.Config,
      embed c1 = embed c2 -> c1 = c2.

  (** Overflow = supercritico nella geometria. *)
  Axiom overflow_implies_supercritical :
    forall c : TM.Config,
      TM.overflow c ->
      Geo.supercritical (embed c).

  (** Stabilità della configurazione = sottocriticità geometrica. *)
  Axiom stable_implies_subcritical :
    forall c : TM.Config,
      TM.stable_conf c ->
      Geo.subcritical (embed c).

  (** Monotonia della complessità: se la complessità di c1 è <= c2,
      lo stesso vale per la Complexity geometrica di embed c1, embed c2. *)
  Axiom complexity_mono :
    forall c1 c2 : TM.Config,
      TM.complexity_conf c1 <= TM.complexity_conf c2 ->
      Geo.Complexity (embed c1) <= Geo.Complexity (embed c2).

  (** Il flusso geometrico simula i passi di TM. *)
  Axiom embed_flow :
    forall (n : nat) (c : TM.Config),
      Geo.Flow n (embed c) = embed (TM.TM_step n c).

  (** Predicato astratto: la configurazione è “polinomiale” (in P) *)
  Parameter polytime_config : TM.Config -> Prop.

  (** Corrispondenza concettuale:
      - polytime_config  <->  contrattibile
      - non polytime     <->  non contrattibile                     *)

  Axiom contractible_iff_polytime :
    forall c : TM.Config,
      polytime_config c <-> Geo.contractible (embed c).

  Axiom divergent_iff_noncontractible :
    forall c : TM.Config,
      (~ polytime_config c) <-> Geo.non_contractible (embed c).

End Loventre_Correspondence.

