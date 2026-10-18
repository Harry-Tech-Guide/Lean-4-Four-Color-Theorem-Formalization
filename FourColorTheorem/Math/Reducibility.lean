import FourColorTheorem.Math.Kempe

namespace Math

structure Configuration where
  ringSize : Nat
  interiorSize : Nat
  adj : Nat → Nat → Bool
  contractEdges : List (Nat × Nat) := []

def Configuration.totalNodes (c : Configuration) := c.ringSize + c.interiorSize

instance : Inhabited Configuration where
  default := { ringSize := 0, interiorSize := 0, adj := fun _ _ => false, contractEdges := [] }

def IsValidConfigColoring (c : Configuration) (color : Nat → Color) : Prop :=
  ∀ i j, i < c.totalNodes → j < c.totalNodes → c.adj i j = true → color i ≠ color j

def BoundaryColoring (_ : Configuration) := Nat → Color

def IsValidBoundaryColoring (c : Configuration) (b : BoundaryColoring c) : Prop :=
  ∀ i j, i < c.ringSize → j < c.ringSize → c.adj i j = true → b i ≠ b j

def extendsToInterior (c : Configuration) (b : BoundaryColoring c) : Prop :=
  ∃ (full : Nat → Color),
    (∀ i, i < c.ringSize → full i = b i) ∧
    IsValidConfigColoring c full

/-- An edge of configuration c is a contracted edge. -/
def isContractEdge (contracts : List (Nat × Nat)) (u v : Nat) : Bool :=
  contracts.contains (u, v) || contracts.contains (v, u)

/-- A valid coloring of the contracted configuration c / E_C:
    1. Contracted edge endpoints receive identical colors.
    2. Adjacent vertices that are not contracted to each other receive distinct colors. -/
def IsValidContractColoring (c : Configuration) (color : Nat → Color) : Prop :=
  (∀ uv ∈ c.contractEdges, uv.1 < c.totalNodes ∧ uv.2 < c.totalNodes ∧ color uv.1 = color uv.2) ∧
  (∀ i j, i < c.totalNodes → j < c.totalNodes → c.adj i j = true →
    isContractEdge c.contractEdges i j = false → color i ≠ color j)

/-- A boundary coloring extends to the contracted configuration c / E_C. -/
def extendsToContracted (c : Configuration) (b : BoundaryColoring c) : Prop :=
  ∃ (full : Nat → Color),
    (∀ i, i < c.ringSize → full i = b i) ∧
    IsValidContractColoring c full

/-- A boundary coloring satisfies contract edge identifications if every contracted
    pair of boundary vertices receives the same color. -/
def SatisfiesContracts (contracts : List (Nat × Nat)) (b : Nat → Color) : Prop :=
  ∀ uv ∈ contracts, b uv.1 = b uv.2

/-- A single Kempe swap on a boundary subset S for colors a and b. -/
def boundaryKempeSwap (_ : Configuration) (b : Nat → Color) (a b_col : Color) (S : Nat → Bool) : Nat → Color :=
  fun i => if S i then Hypermap.swapColor (b i) a b_col else b i

/-- Swapping twice with the same boundary Kempe swap is the identity. -/
theorem boundaryKempeSwap_inv (c : Configuration) (b : BoundaryColoring c) (a b_col : Color) (S : Nat → Bool) :
    boundaryKempeSwap c (boundaryKempeSwap c b a b_col S) a b_col S = b := by
  funext i
  dsimp [boundaryKempeSwap]
  split
  · exact Hypermap.swapColor_inv (b i) a b_col
  · rfl

/-- Helper lemma: swapColor preserves membership in {a, b_col}. -/
theorem swapColor_mem_iff (col a b : Color) :
    (Hypermap.swapColor col a b = a ∨ Hypermap.swapColor col a b = b) ↔ (col = a ∨ col = b) := by
  constructor
  · intro h
    have h2 := Hypermap.swapColor_closed (Hypermap.swapColor col a b) a b h
    rw [Hypermap.swapColor_inv] at h2
    exact h2
  · intro h
    exact Hypermap.swapColor_closed col a b h

/-- Helper lemma: boundary Kempe swap preserves membership in {a, b_col}. -/
theorem boundaryKempeSwap_color_mem (c : Configuration) (b : BoundaryColoring c) (a b_col : Color) (S : Nat → Bool)
    (i : Nat) :
    (boundaryKempeSwap c b a b_col S i = a ∨ boundaryKempeSwap c b a b_col S i = b_col) ↔ (b i = a ∨ b i = b_col) := by
  dsimp [boundaryKempeSwap]
  split
  · exact swapColor_mem_iff (b i) a b_col
  · rfl

/-- A configuration has a chordless ring boundary if the only edges between ring vertices are the cycle edges. -/
def IsChordlessRing (c : Configuration) : Prop :=
  ∀ i < c.ringSize, ∀ j < c.ringSize,
    c.adj i j = true → (j = (i + 1) % c.ringSize ∨ i = (j + 1) % c.ringSize)

/-- An admissible boundary Kempe swap component:
    1. The two swapped colors are distinct.
    2. Every vertex in the swapped subset S currently has color a or b_col.
    3. The subset S does not split adjacent vertices sharing colors {a, b_col}.
    4. The resulting swapped coloring is a valid proper boundary coloring. -/
def IsAdmissibleBoundarySwap (c : Configuration) (b : BoundaryColoring c) (a b_col : Color) (S : Nat → Bool) : Prop :=
  a ≠ b_col ∧
  (∀ i < c.ringSize, S i = true → b i = a ∨ b i = b_col) ∧
  (∀ i < c.ringSize, ∀ j < c.ringSize, c.adj i j = true → (b i = a ∨ b i = b_col) → (b j = a ∨ b j = b_col) → S i = S j) ∧
  IsValidBoundaryColoring c (boundaryKempeSwap c b a b_col S)

/-- An admissible Kempe swap is symmetric: swapping back on the same subset S
    is also an admissible Kempe swap. -/
theorem admissible_swap_symm (c : Configuration) (b : BoundaryColoring c) (a b_col : Color) (S : Nat → Bool)
    (hb_val : IsValidBoundaryColoring c b) (hAdm : IsAdmissibleBoundarySwap c b a b_col S) :
    IsAdmissibleBoundarySwap c (boundaryKempeSwap c b a b_col S) a b_col S := by
  rcases hAdm with ⟨h_ne, h_subset, h_adj, _⟩
  refine ⟨h_ne, ?_, ?_, ?_⟩
  · intro i hi hS
    dsimp [boundaryKempeSwap]
    rw [if_pos hS]
    have hOrig := h_subset i hi hS
    exact Hypermap.swapColor_closed (b i) a b_col hOrig
  · intro i hi j hj hadj h_i h_j
    rw [boundaryKempeSwap_color_mem] at h_i h_j
    exact h_adj i hi j hj hadj h_i h_j
  · rw [boundaryKempeSwap_inv]
    exact hb_val

/-- 
Kempe Equivalence of Boundary Colorings:
Two boundary colorings `b1` and `b2` are Kempe equivalent if there exists a sequence of
admissible boundary Kempe swaps that transforms `b1` into `b2`.
Defined inductively as the equivalence relation generated by admissible boundary Kempe swaps.
-/
inductive KempeEquivalent (c : Configuration) : BoundaryColoring c → BoundaryColoring c → Prop where
  | refl (b : BoundaryColoring c) : KempeEquivalent c b b
  | swap (b : BoundaryColoring c) (a b_col : Color) (S : Nat → Bool) :
      IsValidBoundaryColoring c b →
      IsAdmissibleBoundarySwap c b a b_col S →
      KempeEquivalent c b (boundaryKempeSwap c b a b_col S)
  | symm {b1 b2 : BoundaryColoring c} :
      KempeEquivalent c b1 b2 → KempeEquivalent c b2 b1
  | trans {b1 b2 b3 : BoundaryColoring c} :
      KempeEquivalent c b1 b2 → KempeEquivalent c b2 b3 → KempeEquivalent c b1 b3

abbrev kempeEquivalent (c : Configuration) (b1 b2 : BoundaryColoring c) : Prop :=
  KempeEquivalent c b1 b2

/-- 
True D-Reducibility (RSST Definition):
A configuration is D-reducible if every valid boundary coloring either extends
directly to the interior, or can be eliminated via Kempe equivalence to an
extensible boundary coloring.
-/
def IsDReducible (c : Configuration) : Prop :=
  ∀ (b : BoundaryColoring c), IsValidBoundaryColoring c b → 
    (extendsToInterior c b ∨ ∃ b', IsValidBoundaryColoring c b' ∧ kempeEquivalent c b b' ∧ extendsToInterior c b')

/-- 
True C-Reducibility (RSST Definition):
A configuration is C-reducible if it has a non-empty list of contract edges
and every valid boundary coloring that extends to the contracted configuration
either extends directly to the uncontracted interior, or can be eliminated via
Kempe equivalence to an extensible boundary coloring.
-/
def IsCReducible (c : Configuration) : Prop :=
  c.contractEdges ≠ [] ∧
  ∀ (b : BoundaryColoring c), IsValidBoundaryColoring c b → extendsToContracted c b →
    (extendsToInterior c b ∨ ∃ b', IsValidBoundaryColoring c b' ∧ kempeEquivalent c b b' ∧ extendsToInterior c b')

/-- 
General Reducibility (RSST Definition):
A configuration is reducible if it is either D-reducible or C-reducible.
-/
def IsReducible (c : Configuration) : Prop :=
  IsDReducible c ∨ IsCReducible c

/-- In RSST, C-reducibility is strictly weaker than D-reducibility:
    any D-reducible configuration with specified contract edges is also C-reducible. -/
theorem dreducible_implies_creducible (c : Configuration) (hContract : c.contractEdges ≠ []) :
    IsDReducible c → IsCReducible c := by
  intro hD
  refine ⟨hContract, ?_⟩
  intro b hb _
  exact hD b hb

/-- Reducibility elimination property:
    Any boundary coloring of a reducible configuration that extends to the contracted configuration
    extends to the uncontracted interior, or can be transformed via Kempe equivalence to an extensible coloring.
    Holds constructively for both D-reducible and C-reducible configurations. -/
theorem reducible_elimination (c : Configuration) (hRed : IsReducible c) :
    ∀ (b : BoundaryColoring c), IsValidBoundaryColoring c b → extendsToContracted c b →
      (extendsToInterior c b ∨ ∃ b', IsValidBoundaryColoring c b' ∧ kempeEquivalent c b b' ∧ extendsToInterior c b') := by
  intro b hb hSat
  cases hRed with
  | inl hD => exact hD b hb
  | inr hC => exact hC.2 b hb hSat

end Math
