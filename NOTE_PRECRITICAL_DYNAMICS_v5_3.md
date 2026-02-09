# Loventre Engine — Pre-Critical Dynamics (v5.3)

**Stato:** Congelato
**Data:** Dicembre 2025
**Versione motore:** v5.3
**Rischio epistemico:** Basso
**Claim su P ≠ NP:** Nessuno

---

## 1. Scopo del documento

Questo documento descrive una **dinamica osservativa pre-critica** emersa nel Loventre Engine,
senza introdurre nuove regole decisionali, assiomi o claim teorici forti.

L’obiettivo è **documentare un fenomeno**, non spiegarlo né sfruttarlo operativamente.

---

## 2. Definizione informale di dinamica pre-critica

Nel modello Loventre, una **dinamica pre-critica** è identificata come una configurazione temporale in cui:

* alcune grandezze strutturali crescono rapidamente,
* altre si riducono in modo coordinato,
* senza che sia ancora avvenuto un collasso di regime (black-hole).

La rilevazione avviene **esclusivamente tramite variazioni discrete (Δ)** tra stati consecutivi.

---

## 3. Osservatore pre-critico (livello tecnico)

L’osservatore pre-critico:

* è **puramente descrittivo**,
* non modifica `decision`, `risk_class`, `meta_label`,
* non influisce sul Policy Bridge,
* non introduce soglie globali o universali.

Un evento pre-critico viene segnalato quando **almeno due** delle seguenti condizioni sono soddisfatte:

* incremento significativo di `chi_compactness`
* incremento significativo di `informational_potential`
* decremento significativo di `p_tunnel`

Tutte le condizioni sono valutate **localmente**, tra due step consecutivi.

---

## 4. Risultati empirici per famiglie di problemi

### 4.1 Famiglia 2-SAT

* Nessuna transizione pre-critica persistente osservata.
* Oscillazioni locali non producono accumulo.
* Il regime rimane stabile lungo tutta la sequenza.

**Interpretazione:** dinamica strutturalmente stabile nel modello.

---

### 4.2 Famiglia 3-SAT

* Comparsa di segnali pre-critici in prossimità del passaggio a `meta_P_like_accessible`.
* Breve fase pre-critica seguita da collasso rapido.
* Il collasso coincide con `horizon_flag = true`.

**Interpretazione:** transizione impulsiva senza regime metastabile persistente.

---

### 4.3 Famiglia TSP

* Presenza di segnali pre-critici ripetuti.
* Fase pre-critica **persistente**, con oscillazioni.
* Ritardo significativo prima del collasso finale.

**Interpretazione:** regime metastabile pre-critico nel modello Loventre.

---

## 5. Distinzione chiave introdotta

Il modello distingue ora **tre comportamenti dinamici**, senza modificarne la classificazione formale:

1. **Assenza di pre-criticità** (es. 2-SAT)
2. **Pre-criticità impulsiva** (es. 3-SAT)
3. **Pre-criticità persistente / metastabile** (es. TSP)

Questa distinzione è **dinamica**, non decisionale.

---

## 6. Relazione con l’Invarianza C

* Il regime `C` rimane **invariante** lungo tutta la dinamica osservata.
* La pre-criticità non viola né modifica l’invarianza C.
* La dinamica pre-critica è quindi **compatibile** con il freeze v5.3.

---

## 7. Stato della formalizzazione

* Esiste una formalizzazione Coq della dinamica pre-critica:

  * `Loventre_Precritical_Dynamics.v`
* La formalizzazione è:

  * compilante
  * priva di assiomi
  * separata dal CANON

---

## 8. Decisione di progetto

La dinamica pre-critica viene:

* **documentata**
* **congelata**
* **non utilizzata** per decisioni automatiche

Ogni uso futuro richiederà:

* nuovo seed
* nuova decisione esplicita
* nuova valutazione epistemica

---

**Fine documento.**

