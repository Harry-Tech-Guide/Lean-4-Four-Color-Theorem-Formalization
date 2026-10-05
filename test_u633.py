import sys
with open('FourColorTheorem/Math/U633String.lean', 'r') as f:
    text = f.read()
data = text.split('def u633_data : String := \"')[1].split('\"')[0]
tokens = data.split('|')
r_vals = []
for t in tokens:
    if not t.strip(): continue
    nums = [int(x) for x in t.split()]
    if len(nums) >= 2:
        r_vals.append(nums[1])
import collections
print(collections.Counter(r_vals))
