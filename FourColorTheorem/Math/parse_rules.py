import sys
import pprint

def parse_val(v):
    v = int(v)
    low = v // 10
    upp = v % 10
    if upp == 9: upp = 12
    if low == 0: low = upp
    return (low, upp)

def parse_rules(filename):
    with open(filename, 'r') as f:
        content = f.read()
    
    # We can split by empty lines, since each rule is separated by an empty line in `rules`
    blocks = [b.strip() for b in content.split('\n\n') if b.strip()]
    
    rules = []
    
    for block in blocks:
        lines = [line.strip() for line in block.split('\n') if not line.startswith('#')]
        lines = [line for line in lines if line]
        if not lines:
            continue
        
        parts = lines[0].split()
        rule_num = int(parts[0])
        
        if parts[1] == 'invert':
            rules.append({
                'num': rule_num,
                'invert': True
            })
            continue
            
        b0 = parse_val(parts[1])
        b1 = parse_val(parts[2])
        
        triples = []
        if len(lines) > 1:
            rest = lines[1].split()
            # rest is e.g. ["3", "56", "5", "5"] -> pairs of (vertex, val)
            for i in range(0, len(rest), 2):
                v_idx = int(rest[i])
                val = parse_val(rest[i+1])
                triples.append((v_idx, val))
                
        rules.append({
            'num': rule_num,
            'invert': False,
            'b0': b0,
            'b1': b1,
            'triples': triples
        })
        
    return rules

rules = parse_rules('c:/Four Color Theorem/4ct-main/RSST-code/discharge/rules')
for r in rules[:5]:
    print(r)
