from pathlib import Path
import ast


NEW_DEF = """def append_policy_bridge_to_metrics(metrics: dict) -> dict:
    \"\"\"Integra il Loventre Policy Bridge nelle metrics.

    Aspettative:
    - Usa loventre_local_decision(...) da loventre_policy_bridge_lab se disponibile.
    - Popola:
        * policy_strategy
        * policy_energy
        * policy_comment
      e opzionalmente:
        * policy_bridge_warning
    - Appende una riga testuale di sintesi a meta_explanation, del tipo:
        [Policy Bridge] strategia=...; energia=...; commento=...
    - Restituisce sempre `metrics` (anche in caso di warning).
    \"\"\"

    # Proviamo a importare il Policy Bridge; se fallisce, annotiamo un warning e usciamo.
    try:
        from loventre_policy_bridge_lab import loventre_local_decision
    except Exception as e:
        warning = (
            "Loventre Policy Bridge non disponibile (import fallito: {0})"
        ).format(e)
        metrics["policy_bridge_warning"] = warning
        return metrics

    # Estraiamo i parametri chiave dalle metrics, in modo robusto.
    risk_index = metrics.get("risk_index")
    # Nota: K_globale potrebbe non essere presente a livello di singola istanza.
    k_global = metrics.get("K_globale")
    chi = metrics.get("schwarzschild_compactness")
    gamma_schw = metrics.get("schwarzschild_gamma_dilation")

    # Chiamata protetta al Policy Bridge.
    try:
        decision = loventre_local_decision(
            risk_index=risk_index,
            k_global=k_global,
            chi=chi,
            gamma_schw=gamma_schw,
        )
    except Exception as e:
        warning = (
            "Loventre Policy Bridge ha sollevato un'eccezione: {0}"
        ).format(e)
        metrics["policy_bridge_warning"] = warning
        return metrics

    # Estriamo i campi principali dalla decisione; se non ci sono, annotiamo un warning.
    strategy = getattr(decision, "strategy_decision", None)
    energy_policy = getattr(decision, "energy_policy", None)
    comment = getattr(decision, "comment", None)

    if strategy is None and energy_policy is None and comment is None:
        warning = (
            "Loventre Policy Bridge ha restituito un payload vuoto o non interpretabile."
        )
        metrics["policy_bridge_warning"] = warning
        return metrics

    metrics["policy_strategy"] = strategy
    metrics["policy_energy"] = energy_policy
    metrics["policy_comment"] = comment

    # Costruiamo una riga di sintesi da appiccicare alla meta_explanation.
    base_expl = metrics.get("meta_explanation", "")
    base_expl = (base_expl or "").rstrip()

    bridge_summary = "[Policy Bridge] strategia={0}; energia={1}; commento={2}".format(
        strategy,
        energy_policy,
        comment,
    )

    if base_expl:
        metrics["meta_explanation"] = base_expl + "\\n" + bridge_summary
    else:
        metrics["meta_explanation"] = bridge_summary

    return metrics
"""


def patch_append_policy_bridge(path: Path) -> None:
    text = path.read_text(encoding="utf-8")
    lines = text.splitlines()

    # Trova la def esistente di append_policy_bridge_to_metrics
    start_idx = None
    for i, line in enumerate(lines):
        if line.lstrip().startswith("def append_policy_bridge_to_metrics"):
            start_idx = i
            break

    if start_idx is None:
        print("⚠️  Non trovata def append_policy_bridge_to_metrics; nessuna patch applicata.")
        return

    # Trova l'inizio della prossima funzione (def a colonna zero) oppure EOF.
    end_idx = len(lines)
    for j in range(start_idx + 1, len(lines)):
        if lines[j].startswith("def "):
            end_idx = j
            break

    new_block_lines = NEW_DEF.splitlines()
    new_lines = lines[:start_idx] + new_block_lines + [""] + lines[end_idx:]
    new_text = "\\n".join(new_lines)

    # Verifica sintassi con ast.parse prima di scrivere.
    try:
        ast.parse(new_text)
    except SyntaxError as e:
        print("❌ Errore di sintassi dopo la patch:", e)
        return

    path.write_text(new_text, encoding="utf-8")
    print("✅ append_policy_bridge_to_metrics riscritta senza f-string.")
    print("✅ Sintassi globale di {0} verificata con ast.parse.".format(path))


def main() -> None:
    engine_path = Path("loventre_meta_decision_engine.py")
    if not engine_path.exists():
        print("⚠️  File non trovato:", engine_path)
        return
    patch_append_policy_bridge(engine_path)


if __name__ == "__main__":
    main()

