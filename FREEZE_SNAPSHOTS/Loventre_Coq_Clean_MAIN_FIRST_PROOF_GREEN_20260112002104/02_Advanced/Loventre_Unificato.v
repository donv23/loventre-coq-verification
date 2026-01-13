(** Loventre_Unificato.v
    Vista unificata dei regimi Loventre:
    tempo discreto, profili di istanza, barriere e regimi.

    Versione v2:
      - Niente ridefinizioni del Kernel.
      - Nessun codice TM “storico” o non più allineato.
      - Strato di raccordo sopra i moduli avanzati stabili:
          * Loventre_Time_Regimes
          * Loventre_Barrier_Model
          * Loventre_Tunneling_Model
          * Loventre_Instance_Profile
          * Loventre_Regimes_Definition
          * Loventre_Regimes_Properties
          * Loventre_Lemmas (02_Advanced)
 *)

From Stdlib Require Import List Arith ZArith Lia.

Require Import Loventre_Kernel.
Require Import Loventre_Foundation_Types.
Require Import Loventre_Foundation_Time.
Require Import Loventre_Foundation_History_Structure.
Require Import Loventre_Barrier_Model.
Require Import Loventre_Tunneling_Model.
Require Import Loventre_Time_Regimes.
Require Import Loventre_Instance_Profile.
Require Import Loventre_Regimes_Definition.
Require Import Loventre_Regimes_Properties.
Require Import Loventre_Lemmas.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import ListNotations.
Import Loventre_Geometry.

(* --------------------------------------------------------------- *)
(* 1. Punto unificato: stato dinamico + tempo discreto             *)
(* --------------------------------------------------------------- *)

(** Uno “snapshot” unificato di regime: uno stato dinamico [State]
    osservato a un istante discreto [n : nat]. *)

Record unified_regime_point := {
  ur_state : State;
  ur_time  : nat
}.

(* Profilo associato al punto (x, n); il tipo del profilo è quello
   definito in Loventre_Instance_Profile, che non spezziamo qui. *)
Definition ur_profile (p : unified_regime_point) :=
  build_profile (ur_state p) (ur_time p).

(* Regimi puntuali al tempo [ur_time] *)

Definition ur_regime_subcritical (p : unified_regime_point) : Prop :=
  regime_subcritical_at (ur_state p) (ur_time p).

Definition ur_regime_supercritical (p : unified_regime_point) : Prop :=
  regime_supercritical_at (ur_state p) (ur_time p).

Definition ur_regime_under_barrier (p : unified_regime_point) : Prop :=
  regime_under_barrier_at (ur_state p) (ur_time p).

Definition ur_regime_over_barrier (p : unified_regime_point) : Prop :=
  regime_over_barrier_at (ur_state p) (ur_time p).

(* --------------------------------------------------------------- *)
(* 2. Visione di profilo vs visione puntuale                       *)
(* --------------------------------------------------------------- *)

(** I lemmi seguenti sono semplici “wrappers” dei risultati di
    Loventre_Regimes_Properties, riscritti in termini di
    [unified_regime_point]. *)

Lemma ur_profile_subcritical_iff :
  forall p : unified_regime_point,
    ur_regime_subcritical p <->
    profile_regime_subcritical (ur_profile p).
Proof.
  intros [x n]; simpl.
  apply profile_regime_subcritical_iff_regime_subcritical_at.
Qed.

Lemma ur_profile_supercritical_iff :
  forall p : unified_regime_point,
    ur_regime_supercritical p <->
    profile_regime_supercritical (ur_profile p).
Proof.
  intros [x n]; simpl.
  apply profile_regime_supercritical_iff_regime_supercritical_at.
Qed.

Lemma ur_profile_under_barrier_iff :
  forall p : unified_regime_point,
    ur_regime_under_barrier p <->
    profile_regime_under_barrier (ur_profile p).
Proof.
  intros [x n]; simpl.
  apply profile_regime_under_barrier_iff_regime_under_barrier_at.
Qed.

Lemma ur_profile_over_barrier_iff :
  forall p : unified_regime_point,
    ur_regime_over_barrier p <->
    profile_regime_over_barrier (ur_profile p).
Proof.
  intros [x n]; simpl.
  apply profile_regime_over_barrier_iff_regime_over_barrier_at.
Qed.

(* --------------------------------------------------------------- *)
(* 3. Transizione critica globale                                  *)
(* --------------------------------------------------------------- *)

(** Dal modulo di regimi temporali sappiamo che per ogni [State]
    esiste (assialmente) una transizione critica singola. Qui
    la incapsuliamo in una definizione/lemma “unificata”. *)

Definition ur_has_single_critical_transition (x : State) : Prop :=
  has_single_critical_transition x.

Lemma ur_has_single_critical_transition_holds :
  forall x : State, ur_has_single_critical_transition x.
Proof.
  intro x.
  unfold ur_has_single_critical_transition.
  apply has_single_critical_transition_from_time_regimes.
Qed.

