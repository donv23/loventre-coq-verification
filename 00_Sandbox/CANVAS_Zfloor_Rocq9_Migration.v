(**
  CANVAS_Zfloor_Rocq9_Migration.v
  =================================
  Obiettivo:
    - Mappare il comportamento di Zfloor in Rocq 9.1
    - Identificare lemmi NATIVI da usare
    - Definire regole auree per il Core
    - Evitare ricostruzioni manuali stile Coq 8.x
    - Stabilire pattern di prova compatibili future

  Stato:
    - Rocq 9 usa Stdlib esteso
    - Zfloor / Zceil / up sono definiti e pieni di lemmi nativi
    - "down" NON esiste più
    - Lemmi duplicati tra Zfloor_lub / Zfloor_bound / Zfloor_eq

  Regola aurea:
    Non scrivere mai:
      IZR (Zfloor x) <= x <= IZR (Zfloor x) + 1  come punto di partenza
    MA USARE:
      apply Zfloor_bound.
*)

From Stdlib Require Import Reals ZArith Lia.

Open Scope R_scope.
Open Scope Z_scope.

(**
  LISTA DEI LEMMI CANONICI CHE DOBBIAMO USARE
  (Verificati in Rocq 9.1 via ZZ_Zfloor_Inspect)
*)

(**
 archimed :
   forall r : R, (IZR (up r) > r)%R /\ (IZR (up r) - r <= 1)%R
*)

(**
 ZfloorZ : forall z : Z, Zfloor (IZR z) = z
 Zfloor_le : forall x y, x <= y -> Zfloor x <= Zfloor y
 ZfloorNZ : Zfloor (- IZR z) = - z
 Zfloor_lub : (IZR z <= x -> z <= Zfloor x)
 Zfloor_bound :
    forall x, IZR(Zfloor x) <= x < IZR(Zfloor x)+1
*)

(**
  OSSERVAZIONI CHIAVE RACCOLTE:
  ✔ in Rocq 9.1 si lavora SOLO con Zfloor_bound e Zfloor_le
  ✔ l'espressione di bound è una coppia (<= ∧ <) destruttibile
  ✔ up = Zfloor x + 1 sempre: up_Zfloor
  ✔ Proof idiom:
        assert (Hb := Zfloor_bound x). destruct Hb as [Hlb Hub].
        (* ora Hlb e Hub sono i lower/upper bounds veri *)
*)

(**
  TEMPLATE UNIVERSALE PER PROVE FUTURE
*)

Lemma loventre_floor_is_lower_bound :
  forall x : R, (IZR(Zfloor x) <= x)%R.
Proof.
  intros x.
  pose proof (Zfloor_bound x) as Hb.
  destruct Hb as [Hlb Hub].
  exact Hlb.
Qed.

Lemma loventre_floor_is_upper_bound_strict :
  forall x : R, (x < IZR(Zfloor x) + 1)%R.
Proof.
  intros x.
  pose proof (Zfloor_bound x) as Hb.
  destruct Hb as [Hlb Hub].
  exact Hub.
Qed.

(**
  NEXT STEPS nel progetto Loventre:

  1. Rimpiazzare TUTTI i lemmi personalizzati del passato con:
       - Zfloor_bound
       - Zfloor_le
       - up_Zfloor
       - ZfloorZ (per casi speciali)
       - archimed (per differenze up-floor)
  
  2. NON definire:
       - Zfloor_lb
       - Zfloor_spec
       - Zfloor_floor
       - down
       - equivalenze up/floor manuali
  
  3. Ogni prova deve iniziare con:
       pose proof (Zfloor_bound x) as Hb.
       destruct Hb as [Hlb Hub].
  
  4. Se serve confrontare Zfloor x e Zfloor y:
       apply Zfloor_le.
       (* poi mostra x <= y con lra/lia *)
  
  5. Per P vs NP nel Teorema Loventre:
       Zfloor rappresenta il “gradino minimo”
       del valore fisico/informazionale → prima
       barriera di discrezione!!

  Questo FILE È UN CANVAS.
  Aggiornalo ogni volta che:
    - scopri un lemma
    - verifichi comportamento nuovo
    - individui restrizioni importanti
*)

