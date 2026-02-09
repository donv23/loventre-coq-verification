"""
loventre_audit_logger.py
Audit canonico decisionale Loventre
FASE 4.6
"""

from datetime import datetime
from typing import Dict, Any


def log_decision(record: Dict[str, Any], logfile: str = "loventre_audit.log") -> None:
    """
    Log strutturato e append-only delle decisioni Loventre
    """
    entry = {
        "timestamp": datetime.utcnow().isoformat() + "Z",
        "seed": record.get("seed"),
        "decision": record.get("decision"),
        "mode": record.get("mode"),
        "metrics": {
            "kappa_eff": record["metrics"].get("kappa_eff"),
            "entropy_eff": record["metrics"].get("entropy_eff"),
            "V0": record["metrics"].get("V0"),
            "p_tunnel": record["metrics"].get("p_tunnel"),
            "P_success": record["metrics"].get("P_success"),
        },
    }

    with open(logfile, "a", encoding="utf-8") as f:
        f.write(str(entry) + "\n")

