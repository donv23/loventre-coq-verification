From Coq Require Import List Arith ZArith.
Require Import Loventre_All.
Require Import Loventre_Complexity_Barrier.
Require Import Loventre_Metrics_Bus.
Require Import Loventre_SAT_TSP_Critical_Metrics.

Module Loventre_Main_Theorem.

  (** We reuse the complexity-theoretic module defined in [Loventre_Complexity_Barrier].
      Here we connect it to the geometric side and to the Loventre Metrics Bus. *)

  Module C := Loventre_Complexity.

  (** * Static (complexity-theoretic) side *)

  Definition Word     := C.Word.
  Definition Language := C.Language.
  Definition InP      := C.inP.
  Definition InNP     := C.inNP.

  (** * Dynamic (geometric / flow) side *)

  (** Geometric states are the abstract states from the Loventre geometry. *)
  Definition GeomState := State.

  (** Abstract predicate: a state is a "dynamic Loventre witness". *)
  Parameter Dynamic_witness : GeomState -> Prop.

  (** * Metrics Bus side *)

  Definition BusState := Loventre_Metrics_Bus.LMetrics.

  (** A metrics-level witness: an LMetrics configuration that encodes
      the hardness gap in the bus representation. *)
  Parameter Metrics_witness : BusState -> Prop.

  (** Abstract (but structurally fixed) bridge between bus and geometry. *)
  Parameter geom_of_bus : BusState -> GeomState.
  Parameter bus_of_geom : GeomState -> BusState.

  Axiom Metrics_to_Dynamic :
    forall m : BusState, Metrics_witness m -> Dynamic_witness (geom_of_bus m).

  Axiom Dynamic_to_Metrics :
    forall x : GeomState, Dynamic_witness x -> Metrics_witness (bus_of_geom x).

  (** * SAT/TSP-critical metrics – structural definitions

      Qui agganciamo i predicati [SAT_crit] e [TSP_crit] a definizioni
      esplicite sul bus (campi di [LMetrics]), definite nel modulo
      [Loventre_SAT_TSP_Critical_Metrics].
   *)

  Module Crit := Loventre_SAT_TSP_Critical_Metrics.

  Definition SAT_crit : BusState -> Prop := Crit.SAT_crit.
  Definition TSP_crit : BusState -> Prop := Crit.TSP_crit.

  (** Per ora rimangono assiomi: ogni configurazione SAT/TSP-critica è
      un witness metrico. In futuro questi assiomi sono ottimi candidati
      per diventare teoremi, una volta espansa la struttura di
      [Metrics_witness]. *)

  Axiom SAT_crit_is_metrics_witness :
    forall m : BusState, SAT_crit m -> Metrics_witness m.

  Axiom TSP_crit_is_metrics_witness :
    forall m : BusState, TSP_crit m -> Metrics_witness m.

  (** * Main Loventre theorem – bus-level statement *)

  Axiom Loventre_Theorem_Metrics :
    exists L : Language,
      InNP L /\ ~ InP L /\
      exists m : BusState, Metrics_witness m.

  (** * Main Loventre theorem – geometric / dynamic version *)

  Theorem Loventre_Theorem :
    exists L : Language,
      InNP L /\ ~ InP L /\
      exists x : GeomState, Dynamic_witness x.
  Proof.
    destruct Loventre_Theorem_Metrics as [L [HNP [HnotP [m Hm]]]].
    exists L; split; [assumption | ].
    split; [assumption | ].
    exists (geom_of_bus m).
    apply Metrics_to_Dynamic; assumption.
  Qed.

  (** * High-level corollaries (now derived, not axiomatic) *)

  Theorem Loventre_Corollary_Static :
    exists L : Language, InNP L /\ ~ InP L.
  Proof.
    destruct Loventre_Theorem as [L [HNP [HnotP _]]].
    exists L; split; assumption.
  Qed.

  Theorem Loventre_Corollary_Dynamic :
    exists x : GeomState, Dynamic_witness x.
  Proof.
    destruct Loventre_Theorem as [L [_ [_ [x Hx]]]].
    exists x; exact Hx.
  Qed.

End Loventre_Main_Theorem.

