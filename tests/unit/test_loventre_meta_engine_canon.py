"""
Test – Loventre Meta Engine CANONICAL
"""

import pprint
from loventre_meta_engine_canon import loventre_meta_engine_canon


SEED_GRID = [
    {"param": 1, "factor": 1},
    {"param": 2, "factor": 2},
    {"param": 3, "factor": 3},
]


def main():
    print("\n==============================")
    print(" TEST META ENGINE CANONICO ")
    print("==============================\n")

    for seed in SEED_GRID:
        print("\n" + "=" * 80)
        print("SEED:", seed)
        print("=" * 80)

        result = loventre_meta_engine_canon(seed)

        print("\n--- RISULTATO CANONICO ---")
        pprint.pprint(result, width=120, sort_dicts=False)

        print("\n--- STRUTTURA ---")
        for k in result:
            print(" •", k)

    print("\n==============================")
    print(" FINE TEST ")
    print("==============================\n")


if __name__ == "__main__":
    main()

