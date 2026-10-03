import sys
import re

def parse_hubcap(s):
    # s is like "(1,1,2) (2,2,2) (3,3,2)"
    matches = re.findall(r'\((\d+),(\d+),(-?\d+)\)', s)
    return f"[{', '.join([f'({m[0]}, {m[1]}, {m[2]})' for m in matches])}]"

def parse_tree(lines, idx, expected_lev):
    if idx >= len(lines):
        return "ProofTree.reduce", idx # Should not happen unless EOF
        
    line = lines[idx].strip()
    if line == "Q.E.D.":
        return "ProofTree.reduce", idx
        
    # Match "L<lev> <Type> <args...>"
    # Example: "L0 C  1 -5"
    m = re.match(r'L(\d+)\s+([CRHS])\s*(.*)', line)
    if not m:
        raise ValueError(f"Cannot parse line {idx}: {line}")
        
    lev = int(m.group(1))
    if lev != expected_lev:
        raise ValueError(f"Expected level {expected_lev}, got {lev} at line {idx}: {line}")
        
    node_type = m.group(2)
    args = m.group(3).strip()
    
    if node_type == 'R':
        return "ProofTree.reduce", idx + 1
    elif node_type == 'H':
        hc = parse_hubcap(args)
        return f"ProofTree.hubcap {hc}", idx + 1
    elif node_type == 'S':
        # S 4 1 6 18
        parts = args.split()
        return f"ProofTree.sym {parts[0]} {parts[1]} {parts[2]} {parts[3]}", idx + 1
    elif node_type == 'C':
        parts = args.split()
        v = int(parts[0])
        val = int(parts[1])
        
        true_branch, next_idx = parse_tree(lines, idx + 1, expected_lev + 1)
        false_branch, next_idx2 = parse_tree(lines, next_idx, expected_lev)
        
        return f"ProofTree.cond {v} ({val}) ({true_branch}) ({false_branch})", next_idx2

def generate_lean(degree, filename):
    with open(filename, 'r') as f:
        lines = [line for line in f if line.strip()]
        
    if lines[0].strip() == f"Degree {degree}":
        lines = lines[1:]
        
    tree, idx = parse_tree(lines, 0, 0)
    
    out = f"""import FourColorTheorem.Math.ProofTree

namespace Math
namespace Discharging

def present{degree} : ProofTree :=
  {tree}

end Discharging
end Math
"""
    
    with open(f'c:/Four Color Theorem/FourColorTheorem/Math/Present{degree}.lean', 'w') as f:
        f.write(out)

if __name__ == '__main__':
    generate_lean(7, 'c:/Four Color Theorem/4ct-main/RSST-code/discharge/present7')
    # generate_lean(8, 'c:/Four Color Theorem/4ct-main/RSST-code/discharge/present8')
    # generate_lean(9, 'c:/Four Color Theorem/4ct-main/RSST-code/discharge/present9')
    # generate_lean(10, 'c:/Four Color Theorem/4ct-main/RSST-code/discharge/present10')
    # generate_lean(11, 'c:/Four Color Theorem/4ct-main/RSST-code/discharge/present11')
