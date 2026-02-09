#!/usr/bin/env python3
# ============================================================
#   Loventre Engine - JSON ⇨ Metrics Bridge (Canvas 20)
# ============================================================
#   Questo modulo converte un JSON grezzo (in forma dict) nel
#   bus centrale dei metriche (LMetrics-like) coerente con Coq.
#
#   Chiavi prodotte nel dict finale:
#     - kappa_eff
#     - entropy_eff
#     - V0
#     - p_tunnel
#     - P_success
#     - gamma_dilation
#     - chi_compactness
#     - horizon_flag
#
#   Struttura blindata e anti-clone: hashing contestuale
#   + barrier logico sui campi
# ============================================================

import json
import hashlib

class LoventreJSONBridge:
    @staticmethod
    def _safe_get(d, key, default):
        try:
            v = d.get(key, default)
            if v is None:
                return default
            return v
        except Exception:
            return default

    @staticmethod
    def _integrity_hash(d):
        """
        Protezione anti-clone:
        vincoliamo 4 parametri fondamentali ad hash stabile.
        """
        h = hashlib.sha256()
        for k in ["kappa", "entropy", "barrier", "tunnel"]:
            v = str(LoventreJSONBridge._safe_get(d, k, "NULL"))
            h.update(v.encode("utf-8"))
        return h.hexdigest()

    @staticmethod
    def json_to_metrics(input_json_dict):
        """
        Conversione blindata:
        - traduce chiavi JSON generiche in chiavi metriche Loventre
        - applica hashing di coerenza
        - genera dict "LMetrics-like"
        """
        d = input_json_dict

        kappa_eff       = float(LoventreJSONBridge._safe_get(d, "kappa", 0.0))
        entropy_eff     = float(LoventreJSONBridge._safe_get(d, "entropy", 0.0))
        V0              = float(LoventreJSONBridge._safe_get(d, "barrier", 0.0))
        p_tunnel        = float(LoventreJSONBridge._safe_get(d, "tunnel", 0.0))
        P_success       = float(LoventreJSONBridge._safe_get(d, "success", 0.0))
        gamma_dilation  = float(LoventreJSONBridge._safe_get(d, "gamma", 1.0))
        chi_compactness = float(LoventreJSONBridge._safe_get(d, "chi", 0.0))
        horizon_flag    = int(LoventreJSONBridge._safe_get(d, "horizon", 0))

        protection_hash = LoventreJSONBridge._integrity_hash(d)

        return {
            "kappa_eff"       : kappa_eff,
            "entropy_eff"     : entropy_eff,
            "V0"              : V0,
            "p_tunnel"        : p_tunnel,
            "P_success"       : P_success,
            "gamma_dilation"  : gamma_dilation,
            "chi_compactness" : chi_compactness,
            "horizon_flag"    : horizon_flag,
            "loventre_guard"  : protection_hash
        }

