from pathlib import Path
import re

path = Path("loventre_meta_decision_engine.py")
code = path.read_text()

NEW_FUNC = '''
def append_policy_bridge_to_metrics(metrics: dict) -> dict:
    """
    Integra in modo morbido il Loventre Policy Bridge dentro il dizionario metrics.

    - Non solleva eccezioni critiche: in caso di problemi, aggiunge solo un messaggio
      nella meta_explanation e restituisce metrics invariato.
    - Se il modulo loventre_policy_bridge_lab non è disponibile o loventre_local_decision
      fallisce, il motore continua a funzionare senza policy bridge.
    - Se la decisione viene calcolata, aggiunge:
        metrics["policy_strategy"]
        metrics["policy_energy"]
        metrics["policy_comment"]
      e una riga riassuntiva in metrics["meta_explanation"].
    """
    # Import protetto del Policy Bridge
    try:
        from loventre_policy_bridge_lab import loventre_local_decision  # type: ignore
    except Exception as e:  # noqa: F841
        base = metrics.get("meta_explanation", "")
        msg = f"\\n[Loventre Policy Bridge non disponibile: {e}]"
        metrics["meta_explanation"] = (base + msg).strip()
        return metrics

    # Estrazione robusta delle grandezze chiave
    risk_index = metrics.get("risk_index", 0.0)
    k_global = metrics.get("K_globale", None)
    chi = metrics.get("schwarzschild_compactness", None)
    gamma_schw = metrics.get("gamma_dilation_schwarzschild", None)

    try:
        decision = loventre_local_decision(
            risk_index=risk_index,
            k_global=k_global,
            chi=chi,
            gamma_schw=gamma_schw,
        )
    except Exception as e:  # noqa: F841
        base = metrics.get("meta_explanation", "")
        msg = f"\\n[Loventre Policy Bridge error: {e}]"
        metrics["meta_explanation"] = (base + msg).strip()
        return metrics

    # Estraiamo i campi dalla LoventrePolicyDecision con fallback sicuri
    strategy = getattr(decision, "strategy_decision", None)
    energy_policy = getattr(decision, "energy_policy", None)
    comment = getattr(decision, "comment", "")

    metrics["policy_strategy"] = strategy
    metrics["policy_energy"] = energy_policy
    metrics["policy_comment"] = comment

    base = metrics.get("meta_explanation", "")
    extra = f"\\n- Loventre Policy Bridge: strategy={strategy}, energy={energy_policy}."
    metrics["meta_explanation"] = (base + extra).strip()

    return metrics
'''.lstrip()

# Sostituiamo un'eventuale definizione esistente di append_policy_bridge_to_metrics
pattern = r"\ndef append_policy_bridge_to_metrics\(.*?(?=\ndef |\Z)"
new_code, n = re.subn(pattern, "\n" + NEW_FUNC + "\n\n", code, flags=re.DOTALL)

if n == 0:
    # Nessuna definizione precedente trovata: appendiamo in fondo al file
    new_code = code.rstrip() + "\n\n" + NEW_FUNC + "\n"

path.write_text(new_code)
print("✅ append_policy_bridge_to_metrics riscritta in modo pulito e robusto.")

