(*
  Loventre_GCT_LocalGlobal.v
  ------------------------------------------------------------
  Primo lemma ponte tra GCT e limiti local-to-global.

  Questo file:
  - NON introduce algoritmi
  - NON introduce complessità temporale
  - NON rafforza la GCT
  - NON collega al Main Theorem

  Scopo:
  formalizzare l’impossibilità strutturale
  di una globalizzazione puramente locale
  sotto firma GCT stabile.
*)

From Stdlib Require Import List.
From Stdlib Require Import Bool.
From Stdlib Require Import Arith.

(* Import corretto secondo i -Q reali *)
Require Import Loventre_Advanced.Geometry.Loventre_GCT_Sanity.

(* ------------------------------------------------------------ *)
(* Nozione astratta di strategia locale                         *)
(* ------------------------------------------------------------ *)

Parameter LocalChoice : Type.

Parameter LocalStrategy : Type.
Parameter apply_local : LocalStrategy -> Instance -> LocalChoice.

(* ------------------------------------------------------------ *)
(* Coerenza globale astratta                                    *)
(* ------------------------------------------------------------ *)

Parameter GloballyCoherent : Family -> LocalStrategy -> Prop.

(* ------------------------------------------------------------ *)
(* Firma GCT stabile                                            *)
(* ------------------------------------------------------------ *)

Definition GCT_stable (f : Family) : Prop :=
  diagnose_GCT f = GCT_CONDUCTANCE_COLLAPSE \/
  diagnose_GCT f = GCT_ENTROPIC_BARRIER.

(* ------------------------------------------------------------ *)
(* LEMMA PONTE (INTENZIONALMENTE NON DIMOSTRATO)                *)
(* ------------------------------------------------------------ *)

Lemma GCT_blocks_uniform_local_globalization :
  forall (f : Family),
    GCT_stable f ->
    forall (s : LocalStrategy),
      ~ GloballyCoherent f s.
Proof.
  intros f Hstable s.
  unfold not.
  intro Hcoh.
  (* Frontiera strutturale dichiarata *)
Admitted.

(*
  NOTA:
  Questo Admitted è INTENZIONALE.
  Serve a marcare una barriera strutturale,
  non a chiuderla artificialmente.
*)

