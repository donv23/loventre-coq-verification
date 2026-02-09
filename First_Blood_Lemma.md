# First_Blood_Lemma.md

Tab: SPERIMENTALE_FINALE_PvsNP  
Canvas: 3 — BRIDGE-B  
Status: micro-lemma candidato (nessun claim globale)  
Scopo: formulazione precisa e auditata di ML5 (“first blood”)  
Dipendenze:  
- D1 (robustezza locale di Tseitin)  
- Support_Monotonicity_Def.md  
- SAT_Tseitin_Encoding.md  

---

## 0. Scopo del documento

Questo documento formula in modo preciso il micro-lemma **ML5**
che costituisce il primo punto in cui il programma BRIDGE-B
può produrre un risultato positivo oppure un fallimento informativo pulito.

Il lemma è **locale e condizionale**:
non implica P ≠ NP e non usa trasferimenti automatici.

---

## 1. Contesto

Abbiamo fissato:

- una famiglia esplicita di istanze Tseitin robuste su grafi espansori;
- una codifica CNF locale Tseitin → SAT, senza gadget globali;
- una definizione operativa e non circolare di **Support Monotonicity**.

Il punto critico è verificare se
la riduzione Tseitin → SAT
preserva inevitabilmente il **supporto informazionale globale**.

---

## 2. Nozione di procedura e supporto (chiarimento)

Nel seguito, per **procedura** si intende **qualsiasi meccanismo decisionale**
che, dato in input un’istanza, produce una risposta corretta,
inclusi (ma non limitati a):

- algoritmi deterministici o randomizzati;
- circuiti;
- procedure SAT-specifiche (UP, pure literal, ecc.);
- derivazioni o prove in un sistema formale.

Il **supporto** di una procedura include **ogni forma di accesso informativo**
all’istanza:
- lettura di variabili o clausole,
- uso di proprietà sintattiche,
- sfruttamento di regole semantiche locali.

Non sono ammesse scappatoie basate su “riconoscimento sintattico”
non contabilizzato come supporto.

---

## 3. Statement del micro-lemma (ML5)

### Lemma ML5 — Support Preservation under Tseitin→SAT

Sia:

- \( \mathcal{T}_n \) una famiglia di istanze Tseitin robuste
  su grafi espansori di dimensione \( n \);
- \( R \) la riduzione Tseitin → SAT fissata in
  `SAT_Tseitin_Encoding.md`,
  **localmente strutturata** e **support-monotona**
  nel senso di `Support_Monotonicity_Def.md`.

Allora vale:

> Per ogni procedura \( \mathcal{A}_{SAT} \)
> che decide correttamente la soddisfacibilità di \( R(\mathcal{T}_n) \),
> esiste una costante \( c > 0 \) tale che,
> per infinite istanze,
> \[
> \mathrm{supp}(\mathcal{A}_{SAT}, R(\mathcal{T}_n)) \;\ge\; c \cdot n.
> \]

In particolare:
nessuna procedura con supporto sublineare
può decidere SAT sulle istanze \( R(\mathcal{T}_n) \).

---

## 4. Idea della dimostrazione (proof skeleton)

La dimostrazione segue tre passi concettuali.

### Step 1 — Robustezza locale (D1)

Per ogni insieme di clausole \( S \subseteq R(\mathcal{T}_n) \)
con \( |S| = o(n) \),
esistono due istanze Tseitin
che:

- coincidono su tutte le clausole in \( S \),
- hanno parità globale opposta,
- inducono istanze SAT una soddisfacibile e una insoddisfacibile.

Questo passo usa solo la **località stretta** dell’encoding
(fino a fattori costanti).

---

### Step 2 — Trasferimento via Support Monotonicity

Se esistesse una procedura \( \mathcal{A}_{SAT} \)
che decide \( R(\mathcal{T}_n) \)
usando supporto \( o(n) \),
allora per **Support Monotonicity**
esisterebbe una procedura \( \mathcal{A}_{Tseitin} \)
che decide \( \mathcal{T}_n \)
con supporto \( o(n) \).

L’induzione è **puramente informazionale** ed esistenziale:
non richiede la costruzione effettiva di \( \mathcal{A}_{Tseitin} \).

---

### Step 3 — Contraddizione con NC

Questo contraddice NC per Tseitin-robusto,
che richiede supporto \( \Omega(n) \)
per qualsiasi procedura corretta.

---

## 5. Ipotesi minime usate

Il lemma usa solo:

1. Robustezza locale di Tseitin (D1);
2. Support Monotonicity della riduzione;
3. Encoding SAT localmente strutturato
   (nessuna clausola o variabile vede più di \( O(1) \) vincoli).

Non usa:
- assunzioni randomiche;
- proprietà “large”;
- ipotesi su classi di circuiti specifiche.

---

## 6. Punti di rottura possibili (audit obbligatorio)

Il lemma fallisce se:

- la riduzione non è realmente support-monotona;
- l’encoding SAT introduce gadget non locali;
- esiste una procedura SAT che sfrutta
  una struttura globale non contabilizzata come supporto.

Ogni fallimento deve essere documentato
come **Failure_Report**.

---

## 7. Ruolo nel programma globale

Se ML5 è corretto:

- BRIDGE-B è chiuso per SAT∘R;
- segue una separazione robusta
  in proof complexity / bounded arithmetic
  per famiglie esplicite.

Se ML5 fallisce:

- il fallimento è informativo;
- il programma BRIDGE-B si arresta in modo pulito.

---

## 8. Stato del documento

Questo documento è:
- sperimentale,
- non canonico,
- soggetto a revisione riga per riga.

Nessuna implicazione su P ≠ NP
è valida senza una catena completa e verificata.

