(* ======================================================= *)
(* Bridge_OP_Local.v                                      *)
(* Ponte minimo e corretto tra S3 e D2                    *)
(* ======================================================= *)

Require Import Formal_Core_Abstract.
Require Import CSP_Instance.

(* ------------------------------------------------------- *)
(* Ponte dichiarativo minimo                               *)
(* ------------------------------------------------------- *)

(* Esiste un oggetto astratto che soddisfa OP.
   Questo oggetto è realizzato (a livello informale)
   dall'istanza concreta CSP di S3. *)

Axiom exists_OP_abstract :
  exists X : Formal_Core_Abstract.Obj,
    Formal_Core_Abstract.OP X.

