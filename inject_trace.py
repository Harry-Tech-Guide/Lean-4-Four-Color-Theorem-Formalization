import re

with open('FourColorTheorem/Math/DischargingAlgo.lean', 'r', encoding='utf-8') as f:
    content = f.read()

pattern = r'\|\s*ProofTree\.reduce\s*=>\s*dbg_trace s!"Evaluating reduce!"\s*let res := isReducible configs A_low A_upp \(getAdjMat A_upp\) \(getAdjBool \(getAdjMat A_upp\)\)\s*if not res then dbg_trace s!"isReducible returned false!"\s*res'
replacement = '''| ProofTree.reduce =>
      dbg_trace s!"Evaluating reduce!"
      let res := isReducible configs A_low A_upp (getAdjMat A_upp) (getAdjBool (getAdjMat A_upp))
      if not res then
        dbg_trace s!"isReducible returned false!"
        res
      else
        res'''

content = re.sub(pattern, replacement, content)

with open('FourColorTheorem/Math/DischargingAlgo.lean', 'w', encoding='utf-8') as f:
    f.write(content)
