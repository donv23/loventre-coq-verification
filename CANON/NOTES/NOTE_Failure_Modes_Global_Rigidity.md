# Failure Modes della rigidità globale
## (Nota CANON — Interna)

**Autore:** Vincenzo Loventre  
**Data:** Gennaio 2026  
**Ambito:** Nuova teoria di rigidità (post Cycle 11/12)

---

## Scopo
Questa nota cristallizza risultati **negativi ma definitivi** emersi dai LAB 12.x.
Non sono ipotesi: sono **limiti strutturali verificati** con test formali.

---

## Failure Mode I — Collasso pairwise (LAB-12.2)

### Forma tipica
Definizioni del tipo:


### Risultato
- La “rigidità globale” così definita collassa su un assioma locale
- In particolare: GlobalRigid ≡ IrrevLocal
- Ogni tentativo di dimostrare una separazione è **tautologico per definizione**

### Diagnosi
- Il livello di osservazione è troppo locale
- La proprietà non vede struttura globale
- Coq non segnala l’errore: lo nasconde

### Stato
**Impossibile per definizione.**  
LAB archiviato come risultato negativo.

---

## Failure Mode II — Vacuità strutturale (LAB-12.4 v0)

### Forma tipica
Definizioni globali del tipo:

### Risultato
- In assenza di ipotesi di struttura, la decomposizione non esiste
- La rigidità risulta vera **per vacuità**
- I test mostrano che GlobalRigid è dimostrabile senza ipotesi

### Diagnosi
- Mancanza di vincoli di esistenza (cardinalità, biforcazioni, bacini)
- “Assenza di decomposizione” ≠ “indivisibilità strutturale”

### Stato
**Impossibile per vacuità del dominio.**  
LAB archiviato come risultato negativo.

---

## Lezione strutturale (CANON)

> Ogni nozione sensata di rigidità globale deve essere **condizionata all’esistenza di struttura**.

In particolare:
- Le definizioni **assolute** collassano
- Le definizioni **pairwise** collassano
- Serve una rigidità **relativa** a:
  - bacini non banali
  - reachability non triviale
  - decomposizioni candidate esplicite

---

## Implicazioni strategiche

- Il ramo “P vs NP classico” resta **solo chiarificatorio**
- Il valore della teoria è nella **mappa dei limiti**
- I LAB negativi sono **risultati di primo livello**

---

## Stato finale
Questa nota è **CANON**.
Ogni nuovo LAB sulla rigidità globale deve:
- esplicitare le ipotesi di struttura
- superare questi failure modes
- avere una domanda sì/no chiara

Fine.

