import sys

with open('FourColorTheorem/Math/U633String.lean', 'r') as f:
    text = f.read()

data = text.split('def u633_data : String := "')[1].split('"')[0]
data = data.replace('|', ' ')
nums = [int(x) for x in data.split()]

i = 0
max_d = 0
while i < len(nums):
    r = nums[i]
    if r == 0: break
    i += 1
    size = nums[i]
    i += 1
    
    for _ in range(size):
        pos = i
        total_nodes = r + 0 # Wait, interior size is not known?
        # Just scan until 0
        while nums[pos] != 0:
            pos += 1
        
        # The structure is: 
        # for each node: degree, then degree*neighbors
        # But we don't know totalNodes! 
        # Actually, let's just find the max degree over all configurations.
        break # difficult to parse without totalNodes.

