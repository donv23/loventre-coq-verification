from pathlib import Path
import re

path_engine = Path("loventre_meta_decision_engine.py")
code = path_engine.read_text()

# Rimuove vecchie append_planck_layer_to_metrics se esistono
code = re.sub(r"def\s+append_planck_layer_to_metrics\(.*?\n(?:    .*\n)+?\n", "", code, flags=re.DOTALL)

# Inserisce nuova definizione
insert_block = '''
def append_planck_layer_to_metrics(metrics):
    """Aggiunge il layer Planck–Loventre ai metrics e integra nel meta_explanation."""
    try:
        from loventre_planck_layer import enrich_metrics_with_planck_layer
        metrics = enrich_metrics_with_planck_layer(metrics, overwrite=True)
        if "meta_explanation" in metrics:
            summary = metrics.get("planck_summary", "(no summary)")
            metrics["meta_explanation"] += f"\\n- Strato Planck–Loventre: {summary}"
        return metrics
    except Exception as e:
        metrics["meta_explanation"] = metrics.get("meta_explanation", "") + f"\\n[Planck layer warning: {e}]"
        return metrics

'''

if "append_planck_layer_to_metrics" not in code:
    code = re.sub(r"(def\s+meta_decide_instance_with_mass)", insert_block + r"\1", code)

# Garantisce la chiamata in meta_decide_instance_with_mass
code = re.sub(r"(return\s+metrics)", r"metrics = append_planck_layer_to_metrics(metrics)\n    \1", code)

path_engine.write_text(code)
print("✅ Patch 1 completata: Planck layer integrato nel meta_decision_engine.")

