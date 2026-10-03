with open('4ct-main/configurations/U_633.conf', 'r') as f:
    content = f.read()

import re
blocks = re.split(r'\n\s*\n', content.strip())
compact = []
for b in blocks:
    lines = b.strip().split('\n')
    if len(lines) > 3:
        compact.append(' '.join(lines[1:]).replace('\t', ' '))

compact_str = '|'.join(compact)

with open('FourColorTheorem/Math/U633String.lean', 'w') as f:
    f.write('namespace Math\n\n')
    f.write('/-- Compacted string representation of U_633.conf -/\n')
    f.write('def u633_data : String := "')
    f.write(compact_str)
    f.write('"\n\nend Math\n')
