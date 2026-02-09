# Bridge_Chain.md

Tab: SPERIMENTALE_FINALE_PvsNP  
Canvas: 3 — BRIDGE-B  
Status: bridge tecnico (condizionale, citabile se chiuso)  
Scopo: concatenare SAT∘R → supporto → NC senza salti logici  
Dipendenze:
- D1 (robustezza locale di Tseitin)
- Support_Monotonicity_Def.md
- SAT_Tseitin_Encoding.md
- First_Blood_Lemma.md (ML5)

---

## 0. Scopo del documento

Questo documento chiude formalmente **BRIDGE-B**:
una catena di trasferimento informazionale che collega

> **decisione efficiente di SAT (su istanze esplicite)**  
> → **preservazione del supporto globale**  
> → **violazione di NC per invarianti robusti (Tseitin)**

La catena è **condizionale** e **locale**:
non implica P ≠ NP, ma produce un risultato
**citabile e auditabile** in proof complexity / bounded arithmetic.

---

## 1. Oggetti fissati (input del bridge)

Fissiamo i seguenti oggetti, come definiti nei documenti precedenti:

1. **Istanze Tseitin robuste**
   - Famiglia \( \mathcal{T}_n \) su grafi espansori
   - Invariante: parità globale
   - Proprietà: robustezza locale (D1)

2. **Riduzione Tseitin → SAT**
   - Riduzione \( R \) locale e uniforme
   - Encoding CNF senza gadget globali
   - Località stretta: ogni clausola vede \( O(1) \) vincoli

3. **Support Monotonicity**
   - Definizione operativa non circolare
   - Nessuna procedura può decidere \( B \circ R \)
     con meno supporto di quanto richiesto per \( A \)

---

## 2. Catena del bridge (overview)

La struttura logica del bridge è la seguente:

1. **SAT∘R richiede supporto lineare** (ML5)
2. **Supporto lineare ↔ informazione globale**
3. **Informazione globale ↔ violazione di NC**
4. **Conclusione:** nessuna procedura con supporto sublineare
   decide SAT sulle istanze \( R(\mathcal{T}_n) \)

Ogni freccia è giustificata separatamente.

---

## 3. Anello 1 — SAT∘R → supporto lineare

Per ML5 (First_Blood_Lemma.md):

> Per ogni procedura \( \mathcal{A}_{SAT} \)
> che decide correttamente la soddisfacibilità di \( R(\mathcal{T}_n) \),
> esiste \( c > 0 \) tale che
> \[
> \mathrm{supp}(\mathcal{A}_{SAT}, R(\mathcal{T}_n)) \ge c \cdot n
> \]
> per infinite istanze.

Questo passo usa solo:
- robustezza locale (D1),
- support-monotonicità della riduzione.

---

## 4. Anello 2 — Supporto lineare → informazione globale

Per definizione di **supporto**:

- usare supporto \( \Omega(n) \) significa
  dover accedere a una frazione lineare dell’istanza;
- per l’encoding fissato, ciò equivale ad accedere
  a una frazione lineare dei vincoli di parità locali;
- aggregare tali vincoli è l’unico modo
  per determinare la **parità globale**.

Quindi:
> supporto lineare implica inevitabilmente
> la cattura di un invariante globale.

Questo passo è **puramente informazionale**,
indipendente dal modello computazionale.

---

## 5. Anello 3 — Informazione globale → NC

Per NC (Non-Composizionalità informazionale):

> nessuna procedura corretta
> può determinare l’invariante globale di Tseitin
> usando solo informazione sublineare o localmente composizionale.

Quindi:
- qualsiasi procedura che decidesse SAT∘R
  con supporto sublineare
  violerebbe NC per Tseitin-robusto.

---

## 6. Chiusura del bridge

Combinando gli anelli 1–3:

> Ogni procedura che decide SAT sulle istanze
> \( R(\mathcal{T}_n) \)
> deve necessariamente catturare
> informazione globale robusta,
> e quindi usare supporto \( \Omega(n) \).

Questo chiude **BRIDGE-B** per la famiglia fissata.

---

## 7. Natura del risultato

Il risultato ottenuto è:

- **condizionale** (dipende da Support Monotonicity);
- **locale** (vale per una famiglia esplicita di istanze);
- **non relativizzante** (dipende da struttura informazionale);
- **non naturale** (non usa proprietà “large”).

Non afferma:
- P ≠ NP;
- lower bound universali per SAT.

Afferma:
- un vincolo strutturale forte
  su qualunque tentativo di decisione efficiente
  per SAT su istanze che embed­dano invarianti globali robusti.

---

## 8. Punti di STOP (audit finale)

Il bridge fallisce se:

- Support Monotonicity non è soddisfatta dalla riduzione;
- l’encoding introduce gadget globali nascosti;
- esiste una procedura che aggira il supporto
  senza catturare informazione globale.

Ogni fallimento va documentato
come **Failure_Report** separato.

---

## 9. Stato del documento

Questo documento:
- chiude BRIDGE-B per la famiglia considerata;
- è citabile come risultato intermedio;
- resta sperimentale e non canonico.

Nessuna conseguenza su P ≠ NP
è valida senza ulteriori trasferimenti espliciti.

