import sys

with open('FourColorTheorem/Math/U633String.lean', 'r') as f:
    text = f.read()

data = text.split('def u633_data : String := "')[1].split('"')[0]
data = data.replace('|', ' ')
nums = [int(x) for x in data.split()]
configs = []
i = 0
while i < len(nums):
    r = nums[i]
    if r == 0: break
    i += 1
    size = nums[i]
    i += 1
    verts = []
    for _ in range(size):
        v = []
        while nums[i] != 0:
            v.append(nums[i])
            i += 1
        i += 1
        verts.append(v)
    configs.append((r, size, verts))

print("Config 1:")
print(configs[1])
