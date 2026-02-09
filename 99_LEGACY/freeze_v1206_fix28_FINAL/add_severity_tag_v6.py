#!/usr/bin/env python3

import os, json

ROOT = os.path.dirname(os.path.abspath(__file__)) + "/.."
JSON_DIR = ROOT + "/JSON_IO_v6"

def classify_severity(risk_class, soft_flag):
    if soft_flag == "SOFT":
        return "SOFT_ZONE"
    if risk_class == "LOW":
        return "LOW_SAFE"
    if risk_class == "MEDIUM":
        return "MEDIUM_ALERT"
    if risk_class == "HIGH":
        return "HIGH_RISK"
    return "UNKNOWN"

if __name__ == "__main__":
    print("=== LOVENTRE add_severity_tag_v6 ===")
    for jf in os.listdir(JSON_DIR):
        if jf.endswith(".json"):
            path = f"{JSON_DIR}/{jf}"
            with open(path) as fp:
                data = json.load(fp)

            risk_cls = data.get("risk_class", "LOW")
            soft = data.get("soft_flag", "HARD")
            sev = classify_severity(risk_cls, soft)

            data["severity_tag"] = sev

            with open(path, "w") as fp:
                json.dump(data, fp, indent=2)

            print(f"[PATCHED] {jf} → severity_tag={sev}")

    print("=== DONE: tutti i JSON aggiornati ===")

