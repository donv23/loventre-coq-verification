#!/usr/bin/env python3
import ast
import pathlib
import sys

UV_SENTINEL = "def compute_hawking_uv_regime("


def find_hawking_layer_file(root: pathlib.Path) -> pathlib.Path | None:
    """
    Cerca loventre_hawking_layer.py ovunque sotto root.
    Se ne trova uno solo, lo usa; se nessuno, restituisce None.
    Se più di uno, avvisa e non modifica nulla per sicurezza.
    """
    candidates = list(root.rglob("loventre_hawking_layer.py"))
    if not candidates:
        print("[Loventre] Nessun loventre_hawking_layer.py trovato nel progetto.", file=sys.stderr)
        return None
    if len(candidates) > 1:
        print("[Loventre] ATTENZIONE: trovati più file loventre_hawking_layer.py:", file=sys.stderr)
        for c in candidates:
            print("  -", c, file=sys.stderr)
        print("[Loventre] Per sicurezza non modifico niente. Specificare il file corretto.", file=sys.stderr)
        return None
    return candidates[0]


def main():
    root = pathlib.Path(__file__).resolve().parents[1]
    target = find_hawking_layer_file(root)
    if target is None:
        return

    print(f"[Loventre] Target Hawking layer: {target}")

    original_text = target.read_text(encoding="utf-8")

    # idempotenza: se la funzione esiste già, non facciamo nulla
    if UV_SENTINEL in original_text:
        print("[Loventre] Blocco Hawking UV già presente, nessuna modifica necessaria.")
        return

    block = '''

# === Loventre Hawking UV layer (seed v1) =====================================

def compute_hawking_uv_regime(metrics: dict) -> dict:
    """
    Calcola una piccola firma UV (ultraviolet) sullo stato Hawking a partire dal
    bus centrale `metrics`. Non modifica il dict, restituisce solo un nuovo dict
    con chiavi:
      - 'hawking_uv_index'
      - 'hawking_uv_phase'
      - 'hawking_uv_energy'
      - 'hawking_uv_comment'
    La combinazione è volutamente semplice ma stabile, pensata come primo seed
    per un layer UV curvato.
    """
    if metrics is None:
        raise ValueError("metrics must not be None")

    kappa = float(metrics.get("kappa_eff", 0.0) or 0.0)
    entropy = float(metrics.get("entropy_eff", 0.0) or 0.0)
    V0 = float(metrics.get("V0", 0.0) or 0.0)
    p_tunnel = float(metrics.get("p_tunnel", 0.0) or 0.0)
    risk = float(metrics.get("risk_index", 0.0) or 0.0)

    # combinazione seed: norma euclidea (kappa, entropy) + contributo di barriera
    uv_energy = (kappa ** 2 + entropy ** 2) ** 0.5 + 0.1 * V0

    # indice UV amplificato da tunneling e rischio
    uv_index = uv_energy * (1.0 + 0.5 * p_tunnel + 0.25 * risk)

    # discretizza uv_index in tre fasi qualitative
    if uv_index < 1.0:
        phase = "sub_uv"
        comment = "regime Hawking sotto–curvatura UV"
    elif uv_index < 3.0:
        phase = "critical_uv"
        comment = "regime Hawking UV quasi–critico"
    else:
        phase = "trans_uv"
        comment = "regime Hawking UV trans–critico"

    return {
        "hawking_uv_index": uv_index,
        "hawking_uv_phase": phase,
        "hawking_uv_energy": uv_energy,
        "hawking_uv_comment": comment,
    }


def append_hawking_uv_layer_to_metrics(metrics: dict) -> dict:
    """
    Arricchisce il bus `metrics` con la firma Hawking UV.

    - È safe: se le chiavi UV esistono già, non le tocca (idempotente).
    - Opera in-place ma restituisce comunque `metrics` per chaining.
    - Non modifica nessuna delle chiavi pre-esistenti usate dal motore.
    """
    if metrics is None:
        raise ValueError("metrics must not be None")

    if "hawking_uv_index" in metrics and "hawking_uv_phase" in metrics:
        return metrics

    uv = compute_hawking_uv_regime(metrics)
    metrics.update(uv)
    return metrics
'''

    new_text = original_text.rstrip() + "\n\n" + block.lstrip("\n")

    # Verifica sintattica rigorosa prima di scrivere
    try:
        ast.parse(new_text, filename=str(target))
    except SyntaxError as e:
        print("[Loventre] ERRORE: la patch Hawking UV romperebbe la sintassi, annullo.", file=sys.stderr)
        print(e, file=sys.stderr)
        return

    target.write_text(new_text, encoding="utf-8")
    print(f"[Loventre] Hawking UV layer seed aggiunto a {target}")


if __name__ == "__main__":
    main()

