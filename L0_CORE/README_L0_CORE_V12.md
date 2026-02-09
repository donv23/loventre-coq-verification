# LOVENTRE ENGINE — L0 CORE README (V12)

## Scopo del Layer Core
Il CORE contiene esclusivamente ciò che è *non sperimentale*, *riutilizzabile*, 
e *inerente al motore Loventre* indipendentemente dalla versione LAB.

In V12 il LAB evolve, sperimenta e varia frequente.  
Il CORE invece:
- rimane stabile  
- contiene principi ed utilità non destinate a cambiare rapidamente
- rappresenta le fondamenta su cui V13 e successive versioni si baseranno

---

## Cosa NON deve entrare in `L0_CORE`
❌ euristiche dipendenti da una soglia  
❌ scaling o tuning su alfa/beta  
❌ policy `SAFE vs BLACKHOLE`  
❌ bridging temporanei  
❌ export LAB / JSON demo  
❌ logiche 2-SAT specifiche o demo

---

## Cosa appartiene al CORE
✔ funzioni matematiche di base  
✔ utility generiche (safe_div, clamp01)  
✔ funzioni che misurano *proprietà* indipendenti dal contesto  
✔ oggetti concettuali (kappa_eff, entropy_eff)  
✔ strutture di fusione generiche (merge_dict_safe)

---

## Obiettivo V12
Il V12 LAB deve permetterci di capire:
- quali funzioni vanno “stabilizzate”
- quali sono solo prototipi LAB e NON devono entrare nel CORE
- quali metriche diventano universali

Alla fine del ciclo V12:
→ parte di LAB potrebbe migrare al CORE
→ il resto sarà documentato e lasciato a vivere come LAB puro

---

## Contenuti previsti del CORE (bozza)
- loventre_math.py (curvature math, safe ops)
- loventre_utils.py (merge, clamp)
- loventre_bus_base.py (struttura base bus, senza soglie)
- eventuale layer pubblico API neutro

Nessuna decisione V12 è definitiva:
il CORE resta minimale e privo di soglie.

---

## NOTE VERSIONING
- Questo file documenta lo stato **V12 CORE**
- Nulla va cambiato senza aprire un freeze o nuovo README
- Per integrare modulo nel CORE serve: testcase + coerenza + neutralità

