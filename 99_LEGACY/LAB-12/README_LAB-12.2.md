# LAB-12.2 — Pairwise Global Rigidity (ARCHIVIATO)

**Stato:** LAB IMPOSSIBILE PER DEFINIZIONE  
**Data archiviazione:** Gennaio 2026  
**Autore:** Vincenzo Loventre

## Diagnosi definitiva

LAB-12.2 tentava di mostrare che:

> Irreversibilità locale + isolamento terminale  
> NON implicano rigidità globale

Tuttavia, nel Core era definito:

GlobalRigid ≡ IrrevLocal

cioè:

    Definition GlobalRigid :=
      forall x y, trans x y -> ~ trans y x.

che coincide **definizione-per-definizione** con l’assioma di irreversibilità locale.

## Conseguenza formale

- GlobalRigid è **immediatamente vera** sotto IrrevLocal
- ~GlobalRigid è **logicamente impossibile**
- ogni contromodello fallisce per definizione
- i fallimenti di Coq sono **diagnostici**, non tecnici

## Conclusione scientifica

LAB-12.2 dimostra che:

> Ogni nozione di rigidità globale definita puramente in modo pairwise
> collassa su IrrevLocal ed è quindi inadatta.

Questo è un **risultato negativo strutturale**, da trattato.

LAB-12.2 è quindi **archiviato**, non corretto.

