#!/usr/bin/env python3

import os, json

ROOT = os.path.dirname(os.path.abspath(__file__)) + "/.."
JSON_DIR = ROOT + "/JSON_IO_v6"

def compute_barrier_zone(mass, entropy, risk):
    s = mass + entropy + risk
    if s < 1.0:
        return "GREEN_PASS"
    if s < 2.0:
        return "ORANGE_SQUEEZE"
    return "RED_WALL"

if __name__ == "__main__":
    print("=== LOVENTRE add_barrier_zone_v6 ===")
    for jf in os.listdir(JSON_DIR):
        if jf.endswith(".json"):
            path = f"{JSON_DIR}/{jf}"
            with open(path) as fp:
                data = json.load(fp)

            mass  = data.get("mass_eff", 0)
            entr  = data.get("entropy_eff", 0)
            risk  = data.get("risk_index", 0)

            bz = compute_barrier_zone(mass, entr, risk)

            data["barrier_zone"] = bz

            with open(path, "w") as fp:
                json.dump(data, fp, indent=2)

            print(f"[PATCHED] {jf} → barrier_zone={bz}")

    print("=== DONE: tutti i JSON aggiornati ===")

