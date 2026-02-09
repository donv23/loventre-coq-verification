# Bridge_to_CPpp.md

Tab: SPERIMENTALE_FINALE_PvsNP  
Canvas: 3 — BRIDGE-B  
Status: trasferimento in proof complexity (condizionale, citabile)  
Sistema target: CP** (Cutting Planes con potenziamenti standard)  
Scopo: tradurre BRIDGE-B in un risultato formale su derivazioni CP**  
Dipendenze:
- D1 (robustezza locale di Tseitin)
- Support_Monotonicity_Def.md
- SAT_Tseitin_Encoding.md
- First_Blood_Lemma.md (ML5)
- Bridge_Chain.md

---

## 0. Scopo del documento

Questo documento trasferisce il risultato informazionale
di **BRIDGE-B** nel linguaggio della **proof complexity**,
fissando **CP\*\*** come sistema di riferimento.

L’obiettivo è ottenere un risultato **citabile** del tipo:

> ogni refutazione CP\*\* delle CNF \( R(\mathcal{T}_n) \)
> deve necessariamente usare supporto \( \Omega(n) \)
> (o una misura equivalente di complessità).

Il risultato resta **condizionale** e **locale**:
non implica P ≠ NP.

---

## 1. Sistema di prova: CP\*\*

Nel seguito, **CP\*\*** indica un sistema di tipo Cutting Planes
con le seguenti caratteristiche standard:

- linee che rappresentano disuguaglianze lineari intere;
- regole di inferenza: somma, moltiplicazione per costanti,
  arrotondamento;
- possibilità di introdurre abbreviazioni locali
  (estensioni di dimensione costante).

CP\*\* è scelto perché:
- è sufficientemente potente da simulare molte procedure SAT;
- è compatibile con argomenti informazionali;
- ha collegamenti noti con comunicazione e bounded arithmetic.

---

## 2. Refutazioni CP\*\* e nozione di supporto

### 2.1 Derivazione CP\*\*

Una **refutazione CP\*\*** di una CNF \( \varphi \) è una sequenza
di disuguaglianze che porta a una contraddizione
(es. \( 0 \ge 1 \)) a partire dalle clausole di \( \varphi \).

---

### 2.2 Supporto di una derivazione

Definiamo il **supporto** di una derivazione CP\*\* \( \pi \)
su un’istanza \( \varphi \) come:

> il numero di clausole iniziali di \( \varphi \)
> che sono effettivamente utilizzate (direttamente o indirettamente)
> nella derivazione \( \pi \).

Nota:
- l’uso indiretto include qualunque linea che dipenda
  da una clausola iniziale;
- abbreviazioni o estensioni contano come uso
  delle clausole da cui dipendono.

Questa nozione è coerente con la definizione informazionale
di supporto usata in BRIDGE-B.

---

## 3. Dal SAT algoritmico a CP\*\*

Assumiamo il principio standard (ben noto in proof complexity):

> una procedura efficiente che decide l’insoddisfacibilità
> di una famiglia di CNF induce una famiglia di refutazioni
> efficienti in un sistema di prova sufficientemente forte
> (qui CP\*\*).

Questo passaggio è **condizionale** e serve solo come interfaccia:
il risultato finale è formulato interamente in CP\*\*.

---

## 4. Trasferimento del bridge in CP\*\*

### Lemma CP-Bridge — Support Lower Bound in CP\*\*

Sia \( \varphi_n = R(\mathcal{T}_n) \)
la famiglia di CNF ottenute dalla riduzione Tseitin → SAT.

Allora:

> per ogni refutazione CP\*\* \( \pi_n \) di \( \varphi_n \),
> esiste una costante \( c > 0 \) tale che,
> per infinite istanze,
> \[
> \mathrm{supp}(\pi_n, \varphi_n) \ge c \cdot n.
> \]

In altre parole:
nessuna refutazione CP\*\* può usare
solo un numero sublineare di clausole iniziali.

---

## 5. Idea della dimostrazione

La dimostrazione è una trascrizione diretta di BRIDGE-B:

1. una refutazione CP\*\* con supporto \( o(n) \)
   indurrebbe una procedura SAT con supporto \( o(n) \);
2. per ML5, ciò è impossibile sulle istanze \( \varphi_n \);
3. quindi ogni refutazione CP\*\* richiede supporto \( \Omega(n) \).

L’argomento è:
- informazionale,
- indipendente dalla sintassi specifica di CP\*\*,
- non basato su width o size “classici”.

---

## 6. Natura del risultato

Il risultato ottenuto:

- è **condizionale** (dipende da Support Monotonicity);
- è **locale** (vale per una famiglia esplicita);
- non relativizza;
- non usa proprietà “large”;
- è compatibile con risultati noti su Tseitin e CP.

Non afferma:
- lower bound universali per CP\*\*;
- separazioni di classi classiche.

---

## 7. Punti di STOP (audit proof-complexity)

Il trasferimento fallisce se:

- il passaggio “procedura SAT → refutazione CP\*\*”
  non è giustificabile nel contesto considerato;
- la nozione di supporto CP\*\* non cattura
  tutta l’informazione rilevante;
- CP\*\* ammette scorciatoie globali
  non modellate come supporto.

Ogni fallimento deve essere documentato
come **Failure_Report**.

---

## 8. Stato del documento

Questo documento:

- completa il trasferimento BRIDGE-B → proof complexity;
- costituisce un risultato intermedio citabile;
- resta sperimentale e non canonico.

Nessuna implicazione su P ≠ NP
è valida senza ulteriori passaggi espliciti.

