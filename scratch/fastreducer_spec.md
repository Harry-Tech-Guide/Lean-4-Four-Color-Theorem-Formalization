# FastReducer Specification & Semantic Equivalence to Joint Planar Kempe Elimination

This document provides a formal mathematical and algorithmic specification of the D-reducibility checker implemented in `FourColorTheorem.Math.FastReducer` and `FourColorTheorem.Math.Batch.Runner`, and analyzes its correspondence with the adversarial joint-planar Kempe elimination game defined in `FourColorTheorem.Math.Reducibility`.

---

## 1. Executive Summary & Overview

In the Robertson–Sanders–Seymour–Thomas (RSST) 1997 proof of the Four Color Theorem, a configuration $c$ with ring size $r$ is D-reducible if no counterexample to the Four Color Theorem can contain $c$. Mathematically, this is established by showing that every valid boundary coloring of the ring is *eliminated* under the Kempe chain game.

In `FastReducer.lean` and `Batch/Runner.lean`, D-reducibility is computed via an exact greatest-fixed-point algorithm over the set of non-extendable boundary colorings:
1. **$C_0$ (Initial Live Set):** The set of all valid ring colorings that cannot be extended to a proper 4-coloring of the configuration's interior.
2. **Consistency Fixed Point:** At each iteration, a coloring $\kappa$ survives if and only if for all three color pairings $\theta \in \{1, 2, 3\}$, there exists an *alive* balanced signed non-crossing matching $(M, \mu)$ such that $\kappa$ $\theta$-fits $(M, \mu)$, where a signed matching is alive if *all* $2^{|M|}$ colorings fitting it are currently in the live set.
3. **D-Reducibility Criterion:** If the maximal consistent set (the fixed point) is empty, the configuration is certified D-reducible.

---

## 2. Ring Colorings and Klein Four-Group Edge Traces

### 2.1 The Klein Four-Group $V_4$
The four colors $\{c_0, c_1, c_2, c_3\}$ are identified with the elements of the Klein four-group $V_4 \cong (\mathbb{Z}/2\mathbb{Z})^2$:
- $0 = (0, 0)$
- $1 = (0, 1)$
- $2 = (1, 0)$
- $3 = (1, 1)$

Under this identification, color addition is bitwise XOR: $a \oplus b$. Note that:
- $x \oplus x = 0$ for all $x \in V_4$.
- The non-zero elements $\{1, 2, 3\}$ have order 2.
- The automorphism group $\mathrm{Aut}(V_4) \cong \mathrm{GL}(2, \mathbb{F}_2) \cong S_3$ acts by permuting the three non-zero elements $\{1, 2, 3\}$ while fixing $0$.

### 2.2 Edge Colorings / Traces
Let the ring vertices be indexed cyclically as $0, 1, \dots, r-1$, with ring edges $e_i = (i, (i+1) \bmod r)$ for $0 \le i < r$.

Given a proper vertex coloring $c : \{0, \dots, r-1\} \to V_4$, each ring edge $e_i$ is assigned the color difference:
$$x_i = c(i) \oplus c((i+1) \bmod r) \in \{1, 2, 3\}$$

Because adjacent vertices receive distinct colors, $x_i \ne 0$ for all $i$. Furthermore, summing differences around the cycle yields:
$$\bigoplus_{i=0}^{r-1} x_i = \bigoplus_{i=0}^{r-1} (c(i) \oplus c((i+1) \bmod r)) = 0 \in V_4$$

Conversely, any sequence $(x_0, \dots, x_{r-1}) \in \{1, 2, 3\}^r$ with $\bigoplus_{i=0}^{r-1} x_i = 0$ uniquely determines the vertex coloring up to the choice of $c(0) \in V_4$:
$$c(i) = c(0) \oplus \bigoplus_{k=0}^{i-1} x_k$$
Translating by $c(0)$ merely permutes the four colors globally by the Klein group action, preserving all adjacency constraints and interior extendability.

### 2.3 Base-3 Encoding
`FastReducer` represents an edge trace by digits $d_i = x_i - 1 \in \{0, 1, 2\}$, packed into an integer:
$$\mathrm{idx} = \sum_{i=0}^{r-1} d_i \cdot 3^i \in [0, 3^r)$$
The live set is maintained as a dense `ByteArray` of length $3^r$, providing $O(1)$ membership checks.

### 2.4 $S_3$ Color Symmetry and Orbits
The six permutations of $\{0, 1, 2\}$ correspond to the six automorphisms of $V_4$:
```lean
perms = #[#[0,1,2], #[0,2,1], #[1,0,2], #[1,2,0], #[2,0,1], #[2,1,0]]
```
Because interior extendability is invariant under color permutations fixing 0, the live set remains invariant under $S_3$ throughout the reduction. In `Batch/Runner.lean`, each canonical non-extendable trace is tracked as a 6-element orbit `Orbit6(j0, j1, j2, j3, j4, j5)`. Compacting dead orbits avoids re-scanning all $3^r$ traces.

---

## 3. Non-Crossing Matchings and Signed Matchings

### 3.1 Non-Crossing Partial Matchings
Function `ncMatchings 0 r` generates all non-crossing partial matchings on $\{0, \dots, r-1\}$ via Catalan-style recursion:
```lean
partial def ncMatchings (lo hi : Nat) : Array (Array (Nat × Nat))
```
A matching $M = \{(x_1, y_1), \dots, (x_p, y_p)\}$ satisfies $0 \le x_k < y_k < r$, with disjoint endpoints, such that no two chords cross:
for any $(x_j, y_j)$ and $(x_k, y_k)$, one does not strictly interleave the other.

### 3.2 Role of Unmatched Edges and Transition Edges
Under pairing $\theta_1 = \{\{0, 1\}, \{2, 3\}\}$:
- Difference $1$ connects vertices within the same color pair ($0 \oplus 1 = 1$ and $2 \oplus 3 = 1$).
- Differences $2$ and $3$ cross between the two color pairs ($0 \oplus 2 = 2, 1 \oplus 3 = 2, 0 \oplus 3 = 3, 1 \oplus 2 = 3$).

In `FastReducer`:
- **Unmatched edges** are assigned difference $1$ ($d_i = 0$). They represent ring edges whose endpoints remain in the same Kempe pair $\{0, 1\}$ or $\{2, 3\}$.
- **Matched edges** $x_k, y_k \in M$ are assigned differences from $\{2, 3\}$ ($d \in \{1, 2\}$). They represent boundary *transition edges* between $\{0, 1\}$ ring intervals and $\{2, 3\}$ ring intervals.

### 3.3 Signed Matchings $(M, s)$
A sign assignment $s \in [0, 2^p)$ assigns a sign to each matched pair $k \in \{0, \dots, p-1\}$:
- **Sign $+$ (bit $k$ = 1):** The two transition edges $x_k$ and $y_k$ have *equal* differences (both $2$, or both $3$).
- **Sign $-$ (bit $k$ = 0):** The two transition edges $x_k$ and $y_k$ have *opposite* differences (one $2$, one $3$).

### 3.4 The Balance Parity Condition
In `FastReducer.lean` line 403 and `Batch/Runner.lean` line 53:
```lean
if popcount ((full - 1) - s) % 2 == r % 2
```
Here, $\mathrm{popcount}((2^p - 1) - s)$ counts the number of pairs with sign $-$.

**Why is this condition required?**
Recall that every valid ring trace must satisfy $\bigoplus_{i=0}^{r-1} x_i = 0 \in V_4$.
- The $r - 2p$ unmatched edges each contribute $1 \in V_4$.
- Each $+$ pair has two equal elements from $\{2, 3\}$: $2 \oplus 2 = 0$ and $3 \oplus 3 = 0$. Its XOR sum is $0 \in V_4$.
- Each $-$ pair has one $2$ and one $3$: $2 \oplus 3 = 1 \in V_4$. Its XOR sum is $1 \in V_4$.

Summing over all edges:
$$\bigoplus_{i=0}^{r-1} x_i = ((r - 2p) \cdot 1) \oplus ((\# -) \cdot 1) = (r - 2p + \# -) \cdot 1 \in V_4$$
For this sum to equal $0$, the coefficient must be even:
$$r - 2p + \# - \equiv 0 \pmod 2 \iff \# - \equiv r \pmod 2$$
Thus, **the balance parity condition is necessary and sufficient for the edge differences to sum to 0 in $V_4$**. A signed matching that violates this condition cannot correspond to any valid cycle coloring.

---

## 4. Theta-Fitting

For a balanced signed matching $(M, s)$ with $p$ pairs:
There are $2^p$ parameter choices $t \in [0, 2^p)$.
For each pair $k = (x_k, y_k)$:
- If bit $k$ of $s$ is $1$ ($+$):
  - bit $k$ of $t = 0 \implies (x_k, y_k)$ differences are $(2, 2)$ (`pa`)
  - bit $k$ of $t = 1 \implies (x_k, y_k)$ differences are $(3, 3)$ (`pb`)
- If bit $k$ of $s$ is $0$ ($-$):
  - bit $k$ of $t = 0 \implies (x_k, y_k)$ differences are $(2, 3)$ (`ma`)
  - bit $k$ of $t = 1 \implies (x_k, y_k)$ differences are $(3, 2)$ (`mb`)

All $2^p$ traces generated by `fitIndex m s t` (or recursively in `allFitLive` / `markFitCover`) have:
1. All differences in $\{1, 2, 3\}$.
2. Cyclic XOR sum $= 0$.
Hence every fitting trace is a valid boundary coloring.

---

## 5. Live-Set Fixed Point & D-Reducibility

Let $L_0 \subseteq \{0, \dots, 3^r - 1\}$ be the initial set of non-extendable traces.
At iteration $k \ge 1$:
1. Determine active signed matchings:
   $$\mathrm{Alive}_k = \{(M, s) \in \mathrm{SMData} \mid \forall t \in [0, 2^p),\, \mathrm{fit}(M, s, t) \in L_{k-1}\}$$
2. Compute the $\theta_1$-cover:
   $$\mathrm{Cover}_k = \bigcup_{(M, s) \in \mathrm{Alive}_k} \{\mathrm{fit}(M, s, t) \mid t \in [0, 2^p)\}$$
3. Surviving traces must be covered under all three pairings $\theta \in \{1, 2, 3\}$:
   $$L_k = \{\mathrm{idx} \in L_{k-1} \mid \mathrm{idx} \in \mathrm{Cover}_k \land \mathrm{swap}_{12}(\mathrm{idx}) \in \mathrm{Cover}_k \land \mathrm{swap}_{13}(\mathrm{idx}) \in \mathrm{Cover}_k\}$$
4. Since $L_k \subseteq L_{k-1}$ is finite, the sequence stabilizes at a greatest fixed point $L_\infty$.
5. If $L_\infty = \emptyset$, `checkFast` returns `true` (D-reducible).

---

## 6. Correspondence with the Joint Planar Kempe Game (`Eliminated`)

In `FourColorTheorem.Math.Reducibility`:
```lean
inductive Eliminated (c : Configuration) : BoundaryColoring c → Prop where
  | ext (b : BoundaryColoring c) :
      extendsToInterior c b → Eliminated c b
  | kempe (b : BoundaryColoring c) (θ : ColorPairing)
      (resp : (Nat → Nat → Prop) → (Nat → Nat → Prop) → (Nat → Bool)) :
      IsValidBoundaryColoring c b →
      (∀ (equiv_ab equiv_cd : Nat → Nat → Prop),
        IsJointPlanarRingPartition c b θ equiv_ab equiv_cd →
        IsValidSwapChoice c b θ equiv_ab equiv_cd (resp equiv_ab equiv_cd)) →
      (∀ (equiv_ab equiv_cd : Nat → Nat → Prop),
        IsJointPlanarRingPartition c b θ equiv_ab equiv_cd →
        Eliminated c (boundaryKempeSwap c b θ (resp equiv_ab equiv_cd))) →
      Eliminated c b
```

### 6.1 Encoding of Partitions by Signed Matchings
Consider an exterior planar 4-coloring extending the ring boundary.
Under pairing $\theta = \{\{a, b\}, \{c, d\}\}$:
- The Kempe $ab$-components and $cd$-components partition the exterior disk into regions.
- The boundary curves separating $ab$-regions from $cd$-regions form non-crossing curves ending at the ring boundary.
- Each such curve terminates at two transition edges of the ring cycle, defining a non-crossing matching $M$ of size $p$.
- The orientation of the color swap along each curve determines the sign vector $s \in \{+, -\}^p$.
- Because the exterior graph is planar, the matching $M$ is non-crossing, and the parity of negative pairs matches $r \bmod 2$.
- Thus, every joint planar partition $(\pi_{ab}, \pi_{cd})$ presented by the adversary induces a balanced signed non-crossing matching $(M, s)$.

### 6.2 Kempe Swaps as $\theta$-Fitting Colorings
In the exterior, each $ab$-component and each $cd$-component can be independently swapped or left unchanged.
- Swapping a component corresponds to choosing $S(v) = 1$ on that component.
- On the boundary, swapping toggles the differences of the bounding transition edges by $\oplus 1$ (swapping $2 \leftrightarrow 3$).
- The $2^p$ possible swap decisions across the $p$ independent components generate precisely the $2^p$ traces that $\theta$-fit $(M, s)$.

### 6.3 Soundness Bridge: Induction on Elimination Steps
Suppose `checkFast c sms pow3 = true`, so $L_\infty = \emptyset$.
Each coloring $\kappa$ is eliminated at some stage $\mathrm{stage}(\kappa) < \infty$:
- **$\mathrm{stage}(\kappa) = 0$:** $\kappa \notin L_0$. Then $\kappa$ extends to the interior, so `Eliminated.ext` holds.
- **$\mathrm{stage}(\kappa) = k > 0$:** $\kappa \in L_{k-1} \setminus L_k$.
  By definition of $L_k$, there exists at least one pairing $\theta \in \{1, 2, 3\}$ for which $\kappa$ is NOT covered by any alive matching.
  Let the reducer choose this $\theta$.
  Then for EVERY joint planar partition presented by the adversary:
  1. The partition induces a balanced signed non-crossing matching $(M, s)$ fitting $\kappa$.
  2. Because $\kappa$ is not covered, $(M, s) \notin \mathrm{Alive}_k$.
  3. Therefore, at least one of the $2^p$ fitting colorings $\kappa'$ has $\mathrm{stage}(\kappa') < k$.
  4. The reducer picks the swap choice $S$ corresponding to $\kappa'$.
  5. By the induction hypothesis, $\kappa'$ is eliminated.
  6. Hence, by `Eliminated.kempe`, $\kappa$ is eliminated.

Therefore, every valid boundary coloring is eliminated, proving `IsDReducible c`.

### 6.4 Semantic Conformance Verification
The mathematical semantics of `FastReducer` and `Eliminated` are fully aligned:
1. Both require Kempe swaps to respect planar non-crossing partitions.
2. Both evaluate all three color pairings $\theta \in \{1, 2, 3\}$.
3. The parity constraint on signed matchings is exactly the consistency condition $\sum x_i = 0 \in V_4$ for valid boundary colorings.
4. No structural or semantic discrepancies exist between the executable checker and the game specification.
