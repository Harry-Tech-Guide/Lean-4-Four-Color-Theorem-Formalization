import configs

def load_configs(filepath):
    with open(filepath, 'r') as f:
        content = f.read()
    blocks = [b.strip() for b in content.split('\n\n') if b.strip()]
    confs = []
    for b in blocks:
        lines = b.split('\n')
        if len(lines) > 3:
            # Strip the ID line (e.g., "0.7322")
            clean_code = '\n'.join(lines[1:])
            confs.append(configs.Configuration(clean_code))
    return confs

if __name__ == '__main__':
    print("Loading RSST configurations...")
    confs = load_configs('../configurations/U_633.conf')
    print(f"Loaded {len(confs)} configurations.")
    
    # Check the first configuration (Birkhoff Diamond)
    conf = confs[0]
    print("\n--- Configuration 0 (Birkhoff Diamond) ---")
    print(conf)
    
    print("\nComputing extendable edge colorings (valid boundaries that extend to interior)...")
    # This computes the colorings that extend.
    extendable = conf.extendable_edge_coloring_strings()
    print(f"Number of extendable edge colorings: {len(extendable)}")
    
    print("\nRunning true D-Reducibility check using C-extensions (Kempe chain swaps)...")
    conf.compute_max_consistent_subset()
    res = conf.reducibility_check_output
    
    print(f"\nTrace of consistent subset reduction:")
    print(f"C values: {res['C']}")
    print(f"M values: {res['M']}")
    
    if res['R'] == 'D-reducible':
        print("\nSuccess: Consistent subset reduced to 0.")
        print("This configuration is formally D-REDUCIBLE!")
    else:
        print(f"\nFailure: {res['R']}")
