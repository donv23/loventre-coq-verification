#!/usr/bin/env python3

import os, json

ROOT = os.path.dirname(os.path.abspath(__file__)) + "/.."
JSON_DIR = ROOT + "/JSON_IO_v6"

def classify_soft_flag(risk):
    try:
        return "HARD" if float(risk) < 0.5 else "SOFT"
    except:
        return "HARD"

if __name__ == "__main__":
    print("=== LOVENTRE add_soft_flag_to_json_v6 ===")
    for jf in os.listdir(JSON_DIR):
        if jf.endswith(".json"):
            path = f"{JSON_DIR}/{jf}"
            with open(path) as fp:
                data = json.load(fp)

            risk = data.get("risk_index", 0.0)
            soft = classify_soft_flag(risk)
            data["soft_flag"] = soft

            with open(path, "w") as fp:
                json.dump(data, fp, indent=2)

            print(f"[PATCHED] {jf} → soft_flag={soft}")

    print("=== DONE: tutti i JSON aggiornati ===")

