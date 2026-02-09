# barriers

## Cosa fa

Il layer `barriers/` definisce **incompatibilità strutturali** e **vincoli duri**.

Contiene:
- barriere statiche
- esclusioni logiche
- condizioni di impossibilità
- limiti non negoziabili del modello

Risponde alla domanda:
> “Quali configurazioni sono strutturalmente impossibili o proibite?”

---

## Cosa NON fa

Il layer `barriers/` **NON** deve:
- evolvere nel tempo
- calcolare metriche
- prendere decisioni operative
- applicare policy
- orchestrare flussi

Se una barriera:
- dipende dal tempo
- dipende da una simulazione
- è aggirabile proceduralmente

👉 **non è una barriera.**

---

## Dipendenze consentite

Il layer `barriers/` può importare:
- `core/`
- (eventualmente) tipizzazioni da `regimes/`

Non può importare:
- `metrics/`
- `dynamics/`
- `policy/`
- `experiments/`
- `bridges/`

---

## Ruolo architetturale

Il `barriers/` rende il modello **non triviale**.

Introduce limiti che:
- non dipendono dai dati
- non dipendono dalle scelte
- non dipendono dall’implementazione

