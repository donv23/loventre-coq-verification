(** Loventre_TSP_Critical_Family.v
    Famiglia astratta di istanze TSP_crit_n per il quadro Loventre.

    Obiettivo:
      - Fornire una famiglia F : family (nel senso di Loventre_Conjecture)
        che rappresenti concettualmente le istanze critiche di un problema
        stile TSP.
      - Non spezziamo ancora la struttura interna di [instance]:
        restiamo a livello astratto, ma nominiamo in modo esplicito
        la famiglia e alcune sue proprietà di base.
 *)

From Stdlib Require Import Arith.

Require Import Loventre_Conjecture.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Loventre_TSP_Critical_Family.

  Module Conj := Loventre_Conjecture.Loventre_Conjecture.

  (* ----------------------------------------------------------- *)
  (* 1. Definizione astratta della famiglia TSP_crit             *)
  (* ----------------------------------------------------------- *)

  (** Ogni n identifica un'istanza "critica" TSP_crit_n,
      modellata come un [Conj.instance] astratto. *)

  Parameter TSP_crit_instance : nat -> Conj.instance.

  (** La famiglia associata è semplicemente la mappa n ↦ TSP_crit_instance n. *)
  Definition TSP_crit_family : Conj.family :=
    TSP_crit_instance.

  (* ----------------------------------------------------------- *)
  (* 2. Proprietà di base: taglia e natura NP-like               *)
  (* ----------------------------------------------------------- *)

  (** La dimensione dell'istanza TSP_crit_n cresce almeno linearmente
      con n.  In questa fase la assumiamo come assioma globale. *)

  Axiom TSP_crit_family_size_lower_bound :
    forall n : nat,
      (Conj.size (TSP_crit_family n) >= n)%nat.

  (** La famiglia TSP_crit_family è NP-like critica nel senso Loventre:
      - sta nella classe Loventre_NP_like_critical_family.
      - NON assumiamo qui nulla sulla polytime-ness: quella informazione
        resta nella Congettura globale. *)

  Axiom TSP_crit_family_is_NP_like_critical :
    Conj.Loventre_NP_like_critical_family TSP_crit_family.

End Loventre_TSP_Critical_Family.

