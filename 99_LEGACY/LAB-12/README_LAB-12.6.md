# LAB-12.6 — Structured Global Rigidity (Coq)

**Stato:** FALLITO — Failure Mode IV  
**Tipo:** Instabilità di rappresentazione

## Diagnosi

Ripetuti tentativi di formalizzare una rigidità globale
tramite record concreti (System, Basin, TwoBasins)
producono errori di tipo persistenti in Coq:

    TB : TwoBasins S
    expected : System

L'errore persiste anche quando:
- reach è campo del record
- le proprietà sono esterne ai record
- i parametri sono resi impliciti

## Conclusione

Questo schema di rappresentazione non è stabile in Coq
per proprietà globali di reachability.

Il fallimento è strutturale, non sintattico.

LAB archiviato come Failure Mode IV.

