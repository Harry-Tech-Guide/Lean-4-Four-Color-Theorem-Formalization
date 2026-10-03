import sys

U = [0, 0, 0, 1, 0, 3, 2, 1, 4, 3, 8, 3, 0, 0, 5, 6, 15]
V = [0, 0, 1, 0, 2, 0, 1, 3, 2, 5, 2, 9, 4, 12, 0, 1, 1]

def build_adjmat(deg):
    adjmat = {}
    for i in range(1, deg + 1):
        h = deg if i == 1 else i - 1
        adjmat[(0, h)] = i
        adjmat[(i, 0)] = h
        adjmat[(h, i)] = 0
        a = deg + h
        adjmat[(i, h)] = a
        adjmat[(a, i)] = h
        adjmat[(h, a)] = i
        
        # DoFan for 5, 6, 7 (assuming k=max needed for rules)
        b = deg + i
        c = 2*deg + i
        d = 3*deg + i
        e = 4*deg + i
        
        a_idx = 2*deg if i == 1 else deg + i - 1
        adjmat[(i, a_idx)] = c
        adjmat[(a_idx, c)] = i
        adjmat[(c, i)] = a_idx
        
        adjmat[(i, c)] = d
        adjmat[(c, d)] = i
        adjmat[(d, i)] = c
        
        adjmat[(i, d)] = e
        adjmat[(d, e)] = i
        adjmat[(e, i)] = d
        
        adjmat[(i, e)] = b
        adjmat[(e, b)] = i
        adjmat[(b, i)] = e
    return adjmat

def get_phi(deg, number):
    adjmat = build_adjmat(deg)
    phi = [-1] * 17
    if number > 0:
        phi[0] = 1
        phi[1] = 0
    else:
        phi[0] = 0
        phi[1] = 1
        
    for j in range(2, 17):
        u = phi[U[j]]
        v = phi[V[j]]
        if (u, v) in adjmat:
            phi[j] = adjmat[(u, v)]
        else:
            phi[j] = -1 # Might not exist if degree is too small
    return phi

print("deg=5, num>0:", get_phi(5, 1))
print("deg=5, num<0:", get_phi(5, -1))
