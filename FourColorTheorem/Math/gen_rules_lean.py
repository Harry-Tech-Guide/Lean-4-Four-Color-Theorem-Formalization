import sys

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
    
    blocks = [b.strip() for b in content.split('\n\n') if b.strip()]
    rules = []
    
    for block in blocks:
        lines = [line.strip() for line in block.split('\n') if not line.startswith('#')]
        lines = [line for line in lines if line]
        if not lines: continue
        
        parts = lines[0].split()
        rule_num = int(parts[0])
        
        if parts[1] == 'invert':
            rules[-1]['invert'] = True
            continue
            
        b0 = parse_val(parts[1])
        b1 = parse_val(parts[2])
        
        triples = []
        if len(lines) > 1:
            rest = lines[1].split()
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

def gen_lean():
    rules = parse_rules('c:/Four Color Theorem/4ct-main/RSST-code/discharge/rules')
    
    out = """import Lean
    
namespace Math
namespace Discharging

structure RawRule where
  num : Nat
  b0 : Nat × Nat
  b1 : Nat × Nat
  triples : List (Nat × (Nat × Nat))
  invert : Bool
  deriving Repr, Inhabited, BEq

def theRules : List RawRule := [
"""
    for r in rules:
        trips = ", ".join([f"({v}, ({l}, {u}))" for v, (l, u) in r['triples']])
        out += f"  {{ num := {r['num']}, b0 := ({r['b0'][0]}, {r['b0'][1]}), b1 := ({r['b1'][0]}, {r['b1'][1]}), triples := [{trips}], invert := {str(r['invert']).lower()} }},\n"
    
    out += "  ]\n\n"
    
    # Also dump U and V
    out += "def U : Array Nat := #[0, 0, 0, 1, 0, 3, 2, 1, 4, 3, 8, 3, 0, 0, 5, 6, 15]\n"
    out += "def V : Array Nat := #[0, 0, 1, 0, 2, 0, 1, 3, 2, 5, 2, 9, 4, 12, 0, 1, 1]\n"
    
    out += "\nend Discharging\nend Math\n"
    
    with open('c:/Four Color Theorem/FourColorTheorem/Math/Rules.lean', 'w', encoding='utf-8') as f:
        f.write(out)

if __name__ == '__main__':
    gen_lean()
