# Loventre Coq Verification

Questo repository (`loventre-coq-verification`) contiene la **verifica formale in Coq** del nucleo logico del *Trattato Ultimissimo* di Vincenzo Loventre.

⚠️ **Importante**
Questo lavoro **non rivendica** alcun risultato di complessità computazionale classica (es. P≠NP).
Tutte le separazioni dimostrate sono **interne al modello Loventre** e formalmente circoscritte.

---

## Stato del repository

* **Branch congelato:** `release-2026-01-04-ultimissimo`
* **Tag di riferimento:** `v4-freeze-2026-01-04`
* **Stato:** *freeze formale – stabile per valutazione*

Il codice presente sotto questo branch e tag non è soggetto a modifiche retroattive.

---

## Governance epistemica

Il repository segue una governance epistemica esplicita, basata su una *ladder* dichiarata di assunzioni:

* **A1 – Struttura:** proprietà geometriche e strutturali dimostrate formalmente;
* **A2 – Dinamica:** vincoli ammissibili dichiarati e separati dalle definizioni;
* **A3 – Ipotesi residua:** assunzioni esplicite localizzate, non derivabili da A1/A2.

In particolare, l’esistenza di profili *P-like-accessible* è trattata come **assunzione A3 dichiarata**, senza:

* definizioni per negazione,
* circolarità logica,
* encoding impliciti.

---

## Contenuto del repository

Il repository include esclusivamente:

* definizioni astratte;
* predicati logici;
* lemmi e teoremi Coq;
* script di audit e *smoke test*.

❌ **Non** è incluso alcun motore numerico, simulativo o algoritmico
(oggetto di tutela separata).

---

## Verifica

La consistenza del repository può essere verificata tramite gli script inclusi:

```bash
bash scripts/smoke_src.sh
```

Questi script garantiscono che la catena formale sia internamente coerente e compilabile nello stato congelato.

---

## Documentazione chiave

* `REFEREE_NOTE.md` – Nota sintetica per i referee
* `STATUS_2026-01-04.md` – Stato e freeze v4
* `99_LEGACY_V4/` – Materiale archiviato e versioni precedenti

---

## Licenza e ambito

Questo repository è destinato a **valutazione formale e revisione teorica**.
Ogni uso esterno deve rispettare la distinzione tra:

* risultati **interni al modello Loventre**,
* e complessità computazionale classica.

