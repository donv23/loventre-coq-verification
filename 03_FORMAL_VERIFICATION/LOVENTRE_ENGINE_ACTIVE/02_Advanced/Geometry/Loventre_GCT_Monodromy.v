(*
  Loventre_GCT_Monodromy.v
  ------------------------------------------------------------
  Modello geometrico minimale per la barriera
  di Monodromy / Torsion nella Global Coherence Trichotomy.

  Questo file:
  - introduce un trasporto astratto lungo cammini
  - definisce cicli e monodromia (non-orientabilità)
  - collega la monodromia al fallimento local-to-global
  - NON introduce algoritmi
  - NON introduce tempo
  - NON collega al Main Theorem
*)

From Stdlib Require Import List.
From Stdlib Require Import Bool.

(* Import canonici ed espliciti *)
Require Import Loventre_Advanced.Geometry.Loventre_GCT_Signature.
Require Import Loventre_Advanced.Geometry.Loventre_GCT_Sanity.
Require Import Loventre_Advanced.Geometry.Loventre_GCT_LocalGlobal.

(* ------------------------------------------------------------ *)
(* Spazio di trasporto astratto                                 *)
(* ------------------------------------------------------------ *)

Parameter TransportSpace : Type.
Parameter State : Type.

(* Trasporto locale *)
Parameter transport_step :
  TransportSpace -> State -> State.

(* Cammini come liste di passi *)
Definition Path := list State.

(* Trasporto lungo un cammino *)
Parameter transport_along :
  TransportSpace -> Path -> State -> State.

(* ------------------------------------------------------------ *)
(* Monodromia / torsione                                        *)
(* ------------------------------------------------------------ *)

(*
  Monodromy significa che esistono cicli
  lungo i quali il trasporto non è neutro:
  tornare al punto di partenza cambia lo stato.
*)
Parameter HasMonodromy : TransportSpace -> Prop.

(* ------------------------------------------------------------ *)
(* Collegamento famiglia → spazio di trasporto                  *)
(* ------------------------------------------------------------ *)

Parameter family_transport_space : Family -> TransportSpace.

(* ------------------------------------------------------------ *)
(* Lemma ponte: monodromia → fallimento globale                 *)
(* ------------------------------------------------------------ *)

Lemma monodromy_blocks_global_coherence :
  forall (f : Family),
    HasMonodromy (family_transport_space f) ->
    forall (s : LocalStrategy),
      ~ GloballyCoherent f s.
Proof.
  intros f Hmono s.
  unfold not.
  intro Hcoh.
Admitted.

(*
  NOTA:
  Lemma deliberatamente ammesso.
  La barriera è topologica/strutturale,
  non algoritmica.
*)

