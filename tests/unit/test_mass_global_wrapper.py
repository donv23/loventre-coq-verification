from loventre_meta_decision_engine import meta_decide_instance_with_mass_global


def main() -> None:
    print("[Loventre] Wrapper importato correttamente:")
    print("  nome funzione:", meta_decide_instance_with_mass_global.__name__)
    print()
    print("  docstring (prime righe):")
    doc = (meta_decide_instance_with_mass_global.__doc__ or "").strip().splitlines()
    for line in doc[:8]:
        print("   ", line)


if __name__ == "__main__":
    main()

