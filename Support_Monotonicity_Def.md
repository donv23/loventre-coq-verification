# Support_Monotonicity_Def.md

Tab: SPERIMENTALE_FINALE_PvsNP  
Status: definizione operativa (nessun claim)  
Dipendenze: NC, robustezza locale (Tseitin), preservazione del supporto  
Uso consentito: BRIDGE-B, ML5  
Uso vietato: trasferimenti automatici al CANON

---

## 0. Scopo del documento

Questo documento introduce una **definizione operativa di Support Monotonicity**
per riduzioni da problemi con **invarianti globali robusti** (es. Tseitin)
a SAT (o problemi NP-completi analoghi).

La definizione serve a:
- impedire che una riduzione “nasconda” informazione globale,
- rendere attaccabile il micro-lemma ML5,
- fornire un criterio chiaro di **STOP** per l’intero programma BRIDGE-B.

Questo documento **non contiene teoremi** e **non implica alcuna separazione**.

---

## 1. Invarianti globali e supporto

### 1.1 Invariante globale

Un **invariante globale** è una proprietà \( I(x) \) di un’istanza \( x \) tale che:

- \( I(x) \) non è determinabile da alcuna vista locale di dimensione \( o(n) \);
- esistono istanze \( x, x' \) che coincidono su ogni sottoinsieme locale \( S \)
  con \( |S| = o(n) \), ma con \( I(x) \neq I(x') \).

Esempio canonico:
- la **parità globale** in istanze Tseitin su grafi espansori.

---

### 1.2 Supporto

Dato:
- un problema decisionale \( P \),
- un’istanza \( x \in P \),
- una procedura \( \mathcal{A} \) (algoritmo, circuito, prova, derivazione),

definiamo il **supporto** di \( \mathcal{A} \) su \( x \), denotato
\( \mathrm{supp}(\mathcal{A}, x) \), come:

> la quantità minima di informazione dell’istanza
> che \( \mathcal{A} \) deve effettivamente utilizzare
> per determinare l’output corretto su \( x \).

Informalmente:
- quali variabili, clausole, assiomi, bit di input
  sono *necessari* (non solo accessibili).

---

### 1.3 Supporto e NC

Diremo che un invariante globale \( I \) **rispetta NC** se vale:

> per ogni procedura \( \mathcal{A} \) che decide correttamente \( I \),
> esiste una costante \( c > 0 \) tale che
> \( \mathrm{supp}(\mathcal{A}, x) \ge c \cdot n \)
> per infinite istanze \( x \).

Questo formalizza il fatto che
**l’informazione globale non è comprimibile localmente**.

---

## 2. Riduzioni e perdita di informazione

Sia:
- \( A \) un problema con invariante globale robusto \( I_A \),
- \( B \) un problema target (es. SAT),
- \( R \) una riduzione da \( A \) a \( B \).

Intuitivamente, una riduzione è *pericolosa* se:
- codifica \( I_A \) in una forma tale che
- una procedura per \( B \) può decidere l’output
  senza “pagare” il costo informazionale di \( I_A \).

Questo è il punto dove **molti tentativi storici falliscono**.

---

## 3. Definizione di Support Monotonicity

### 3.1 Definizione (Support Monotonicity)

Una riduzione \( R : A \to B \) è **support-monotona** se vale la seguente proprietà:

> Per ogni procedura \( \mathcal{A}_B \) che decide \( B \circ R \),
> esiste una procedura \( \mathcal{A}_A \) che decide \( A \)
> tale che, per ogni istanza \( x \in A \),
>
> \[
> \mathrm{supp}(\mathcal{A}_A, x)
> \;\;\le\;\;
> \mathrm{supp}(\mathcal{A}_B, R(x)) + O(1).
> \]

In altre parole:
- nessuna procedura può decidere \( B \circ R \)
  usando *meno supporto*
  di quanto sia necessario per decidere \( A \).

---

### 3.2 Interpretazione informazionale

Support Monotonicity afferma che:

- la riduzione **non distrugge**
  l’invariante globale,
- non lo “diluisce” in gadget locali,
- non lo trasforma in una proprietà
  accessibile con viste sublineari.

Se una riduzione viola questa proprietà,
**non è ammessa** nel programma BRIDGE-B.

---

## 4. Esempio ammesso (intuitivo)

Riduzione che:
- mappa ogni vincolo globale in un insieme di clausole
  distribuite linearmente sull’istanza,
- tale che qualsiasi decisione corretta
  richiede ispezionare una frazione lineare delle clausole.

Queste riduzioni **amplificano** il supporto
o lo preservano.

---

## 5. Esempio non ammesso (STOP-case)

Riduzione che:
- introduce una singola clausola “chiave”
  o un gadget di dimensione \( O(1) \),
- da cui è ricostruibile l’invariante globale,
- indipendentemente dal resto dell’istanza.

In questo caso:
- \( \mathrm{supp}(\mathcal{A}_B, R(x)) = O(1) \),
- mentre \( \mathrm{supp}(\mathcal{A}_A, x) = \Omega(n) \).

Questa è **una violazione diretta** di Support Monotonicity
e comporta **STOP immediato** del programma.

---

## 6. Criteri di STOP (vincolanti)

Il programma BRIDGE-B si arresta se:

- non esiste alcuna riduzione support-monotona nota o plausibile;
- la definizione collassa a una tautologia (“tutte le riduzioni buone”);
- la monotonicità richiede ipotesi “large” o non verificabili;
- la riduzione maschera il supporto tramite encoding artificiale.

---

## 7. Ruolo nel programma

Se esiste una riduzione support-monotona
da Tseitin-robusto a SAT, allora:

- ML5 è formulabile in modo rigoroso;
- BRIDGE-B diventa attaccabile;
- un fallimento sarà **informativo**, non ambiguo.

Se **non esiste**, il programma si ferma qui,
con un risultato negativo chiaro e citabile.

---

## 8. Stato del documento

Questo documento è:
- sperimentale,
- non canonico,
- soggetto a revisione.

Nessuna conseguenza su P ≠ NP è implicata
senza una catena completa e auditata.

