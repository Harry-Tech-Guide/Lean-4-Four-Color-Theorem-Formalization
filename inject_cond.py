import re

with open('FourColorTheorem/Math/DischargingAlgo.lean', 'r', encoding='utf-8') as f:
    content = f.read()

pattern = r'let bTrue := verifyTree configs deg AA_low_true AA_upp_true trueBranch outs\s+if not bTrue then\s+dbg_trace "Failure in cond"\s+return false\s+else return verifyTree configs deg AA_low_false AA_upp_false falseBranch outs'

replacement = '''let bTrue := verifyTree configs deg AA_low_true AA_upp_true trueBranch outs
      if not bTrue then
        dbg_trace s!"Failure in cond {v} {m} (trueBranch failed)"
        return false
      else
        let bFalse := verifyTree configs deg AA_low_false AA_upp_false falseBranch outs
        if not bFalse then
          dbg_trace s!"Failure in cond {v} {m} (falseBranch failed)"
        return bFalse'''

content = re.sub(pattern, replacement, content)

with open('FourColorTheorem/Math/DischargingAlgo.lean', 'w', encoding='utf-8') as f:
    f.write(content)
