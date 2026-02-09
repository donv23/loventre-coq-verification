#!/usr/bin/env python3
"""
Patch Hawking UV → Policy Bridge:
- aggiunge un helper _compute_hawking_uv_risk_coupling(...)
- collega l'helper dentro apply_policy_bridge_to_metrics(...)
in modo idempotente e validato con ast.parse.
"""
import ast
import pathlib
import re
import sys
import textwrap


def _safe_parse(src: str, label: str) -> None:
    try:
        ast.parse(src)
    except SyntaxError as e:
        print(f"[ERROR] Syntax error while parsing {label}: {e}")
        sys.exit(1)


def main() -> None:
    root = pathlib.Path(__file__).resolve().parents[1]
    target = root / "loventre_meta_decision_engine.py"

    if not target.exists():
        print(f"[ERROR] Target file not found: {target}")
        sys.exit(1)

    original = target.read_text(encoding="utf-8")
    _safe_parse(original, "original loventre_meta_decision_engine.py")

    updated = original

    # 1. Helper _compute_hawking_uv_risk_coupling se assente
    if "_compute_hawking_uv_risk_coupling" not in updated:
        helper_block = textwrap.dedent("""
        def _compute_hawking_uv_risk_coupling(metrics: dict) -> dict:
            \"""
            Integra le grandezze Hawking UV dentro un canale di rischio accoppiato.
            - Legge: risk_index, hawking_uv_index, hawking_uv_phase, hawking_uv_energy.
            - Scrive:
                * risk_index_hawking_coupled
                * risk_index_hawking_delta
                * hawking_uv_risk_comment
            - Aggiorna inoltre metrics["risk_index"] in modo controllato, lasciando traccia della base.
            \"""
            # Se non c'è un rischio di base, non facciamo nulla
            if "risk_index" not in metrics:
                return metrics

            base = metrics.get("risk_index", 0.0)
            try:
                base_val = float(base)
            except Exception:
                # Non forziamo la mano se il valore è bizzarro
                return metrics

            hv_index = metrics.get("hawking_uv_index", 0.0)
            hv_phase = metrics.get("hawking_uv_phase", "unknown")
            hv_energy = metrics.get("hawking_uv_energy", 0.0)

            # Normalizzazione molto compressa: riportiamo l'indice UV in [0, 1]
            try:
                raw_idx = float(hv_index or 0.0)
            except Exception:
                raw_idx = 0.0
            raw_idx = max(0.0, raw_idx)
            uv_scale = raw_idx / (100.0 + raw_idx)  # ~lineare per valori piccoli, saturato verso 1

            # Piccolo termometro sull'energia UV, anche qui compresso
            try:
                e_uv = float(hv_energy or 0.0)
            except Exception:
                e_uv = 0.0
            e_uv = max(0.0, e_uv)
            energy_scale = e_uv / (50.0 + e_uv)

            # Peso di fase: sub_uv tende a ridurre leggermente il rischio,
            # critical_uv lo mantiene/sfiora, trans_uv lo amplifica un po' di più.
            phase = str(hv_phase or "unknown")
            if phase == "sub_uv":
                phase_sign = -0.4
            elif phase == "critical_uv":
                phase_sign = 0.3
            elif phase == "trans_uv":
                phase_sign = 0.6
            else:
                phase_sign = 0.0

            # Delta frazionario massimo molto piccolo, per non distruggere la scala di rischio:
            # combinazione morbida di indice e energia UV.
            mixed_scale = 0.6 * uv_scale + 0.4 * energy_scale
            # range teorico ~[-0.036, +0.054] prima del clamp finale
            delta_frac = phase_sign * 0.15 * mixed_scale
            # Clamp finale: delta frazionario in [-0.08, +0.12]
            delta_frac = max(-0.08, min(0.12, delta_frac))

            coupled = base_val * (1.0 + delta_frac)

            # Traccia separata: manteniamo il valore di base se non esiste già
            if "risk_index_hawking_base" not in metrics:
                metrics["risk_index_hawking_base"] = base_val

            metrics["risk_index_hawking_coupled"] = coupled
            metrics["risk_index_hawking_delta"] = coupled - base_val

            # Commento descrittivo, utile per il meta–report
            if delta_frac > 0.01:
                trend = "amplificato dal canale Hawking UV"
            elif delta_frac < -0.01:
                trend = "leggermente attenuato dal canale Hawking UV"
            elif abs(delta_frac) <= 1e-6:
                trend = "praticamente neutro rispetto al canale Hawking UV"
            else:
                trend = "solo modulato in modo molto lieve dal canale Hawking UV"

            metrics["hawking_uv_risk_comment"] = (
                f"risk_index adattato in modo morbido ({delta_frac:+.3f}) "
                f"in fase {phase} con indice UV ≈ {raw_idx:.3f}."
                f" Effetto: {trend}."
            )

            # Piccolo aggiornamento effettivo: qui scegliamo deliberatamente
            # di usare il valore accoppiato come nuovo risk_index
            metrics["risk_index"] = coupled
            return metrics
        """)
        updated = updated.rstrip() + "\n\n" + helper_block + "\n"
        _safe_parse(updated, "after adding _compute_hawking_uv_risk_coupling")
    else:
        print("[INFO] Helper already present, skipping helper injection.")

    # 2. Collegare il canale Hawking UV dentro apply_policy_bridge_to_metrics(...)
    pattern = r"(def\s+apply_policy_bridge_to_metrics\s*\([^)]*\)\s*:[^\n]*\n)([\s\S]*?)(\n\s*return\s+metrics\b)"
    match = re.search(pattern, updated)
    if not match:
        print("[WARN] Could not locate apply_policy_bridge_to_metrics; no call injected.")
    else:
        header, body, ret = match.groups()
        if "_compute_hawking_uv_risk_coupling" in body or "_compute_hawking_uv_risk_coupling" in ret:
            print("[INFO] Policy Bridge already calls helper; skipping injection.")
        else:
            indent_match = re.search(r"\n(\s*)return\s+metrics\b", ret)
            indent = indent_match.group(1) if indent_match else "    "
            call_line = f"\n{indent}metrics = _compute_hawking_uv_risk_coupling(metrics)"
            new_ret = call_line + ret
            updated = updated[: match.start()] + header + body + new_ret + updated[match.end() :]
            _safe_parse(updated, "after wiring helper into apply_policy_bridge_to_metrics")

    if updated != original:
        target.write_text(updated, encoding="utf-8")
        print("[OK] Patch applied to loventre_meta_decision_engine.py")
    else:
        print("[OK] Nothing to change; file already patched.")


if __name__ == "__main__":
    main()

