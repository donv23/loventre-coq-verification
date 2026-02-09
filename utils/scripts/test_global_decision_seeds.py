import os
import sys

# Assicuriamo che la root del progetto sia nel sys.path
ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if ROOT not in sys.path:
    sys.path.insert(0, ROOT)

from loventre_meta_engine import meta_analyze_seed
from loventre_meta_decision_engine import loventre_global_decision


def main() -> None:
    E = 0.5  # energia meta per il test

    print("=== Loventre global decision sulla seed grid {1,2,3}x{1,2,3} ===")
    for param in [1, 2, 3]:
        for factor in [1, 2, 3]:
            metrics = meta_analyze_seed(param, factor, E)
            g = loventre_global_decision(metrics, family="seed_grid")

            print(
                f"seed=({param},{factor}) -> "
                f"{g['global_decision']:8s} "
                f"{g['global_color']:5s} "
                f"score={g['global_score']:.3f}"
            )


if __name__ == "__main__":
    main()

