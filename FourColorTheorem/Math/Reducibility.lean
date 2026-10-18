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

/-- A valid planar ring partition for a boundary coloring b and distinct colors a, b_col:
    1. It is reflexive on ring vertices colored a or b_col.
    2. It is symmetric.
    3. It is transitive.
    4. It strictly only relates ring vertices colored a or b_col.
    5. Ring boundary adjacency connects vertices in the same Kempe component.
    6. Non-crossing planarity (Jordan curve theorem): alternating vertices must merge. -/
def IsPlanarRingPartition (c : Configuration) (b : BoundaryColoring c) (a b_col : Color)
    (equiv : Nat → Nat → Prop) : Prop :=
  (∀ i < c.ringSize, (b i = a ∨ b i = b_col) → equiv i i) ∧
  (∀ i < c.ringSize, ∀ j < c.ringSize, equiv i j → equiv j i) ∧
  (∀ i < c.ringSize, ∀ j < c.ringSize, ∀ l < c.ringSize, equiv i j → equiv j l → equiv i l) ∧
  (∀ i < c.ringSize, ∀ j < c.ringSize, equiv i j → (b i = a ∨ b i = b_col)) ∧
  (∀ i < c.ringSize, ∀ j < c.ringSize, c.adj i j = true → (b i = a ∨ b i = b_col) → (b j = a ∨ b j = b_col) → equiv i j) ∧
  (∀ i j l m, i < j → j < l → l < m → m < c.ringSize →
    equiv i l → equiv j m → equiv i j)

/-- A valid swap choice S over a planar ring partition:
    1. S only contains ring vertices colored a or b_col.
    2. S is a union of equivalence classes of equiv (swaps entire components). -/
def IsValidSwapChoice (c : Configuration) (b : BoundaryColoring c) (a b_col : Color)
    (equiv : Nat → Nat → Prop) (S : Nat → Bool) : Prop :=
  (∀ i < c.ringSize, S i = true → (b i = a ∨ b i = b_col)) ∧
  (∀ i < c.ringSize, ∀ j < c.ringSize, equiv i j → S i = S j)

/-- An admissible swap choice over a planar partition preserves boundary coloring validity. -/
theorem swap_preserves_valid (c : Configuration) (b : BoundaryColoring c) (a b_col : Color)
    (equiv : Nat → Nat → Prop) (S : Nat → Bool)
    (hb : IsValidBoundaryColoring c b)
    (hPart : IsPlanarRingPartition c b a b_col equiv)
    (hSwap : IsValidSwapChoice c b a b_col equiv S) :
    IsValidBoundaryColoring c (boundaryKempeSwap c b a b_col S) := by
  intro i j hi hj hadj
  dsimp [boundaryKempeSwap]
  cases hSi : S i <;> cases hSj : S j
  · dsimp
    exact hb i j hi hj hadj
  · dsimp
    intro h_eq
    have h_mem_j : b j = a ∨ b j = b_col := hSwap.1 j hj hSj
    have h_swapped_mem : Hypermap.swapColor (b j) a b_col = a ∨ Hypermap.swapColor (b j) a b_col = b_col :=
      Hypermap.swapColor_closed (b j) a b_col h_mem_j
    rw [← h_eq] at h_swapped_mem
    have h_equiv_ij := hPart.2.2.2.2.1 i hi j hj hadj h_swapped_mem h_mem_j
    have h_S_eq := hSwap.2 i hi j hj h_equiv_ij
    rw [hSi, hSj] at h_S_eq
    contradiction
  · dsimp
    intro h_eq
    have h_mem_i : b i = a ∨ b i = b_col := hSwap.1 i hi hSi
    have h_swapped_mem : Hypermap.swapColor (b i) a b_col = a ∨ Hypermap.swapColor (b i) a b_col = b_col :=
      Hypermap.swapColor_closed (b i) a b_col h_mem_i
    rw [h_eq] at h_swapped_mem
    have h_equiv_ij := hPart.2.2.2.2.1 i hi j hj hadj h_mem_i h_swapped_mem
    have h_S_eq := hSwap.2 i hi j hj h_equiv_ij
    rw [hSi, hSj] at h_S_eq
    contradiction
  · dsimp
    intro h_eq
    have h_orig := Hypermap.swapColor_inj _ _ _ _ h_eq
    exact hb i j hi hj hadj h_orig

/-- 
Adversarial Kempe Elimination (Gonthier / RSST):
A boundary coloring is eliminated if:
1. It extends directly to the interior, or
2. The reducer can choose colors a ≠ b_col such that for EVERY planar partition equiv
   presented by the exterior graph (the adversary), there is a valid swap choice S
   (a union of equiv components) such that the swapped coloring is eliminated.
-/
inductive Eliminated (c : Configuration) : BoundaryColoring c → Prop where
  | ext (b : BoundaryColoring c) :
      extendsToInterior c b → Eliminated c b
  | kempe (b : BoundaryColoring c) (a b_col : Color)
      (resp : (Nat → Nat → Prop) → (Nat → Bool)) :
      IsValidBoundaryColoring c b →
      a ≠ b_col →
      (∀ (equiv : Nat → Nat → Prop), IsPlanarRingPartition c b a b_col equiv →
        IsValidSwapChoice c b a b_col equiv (resp equiv)) →
      (∀ (equiv : Nat → Nat → Prop), IsPlanarRingPartition c b a b_col equiv →
        Eliminated c (boundaryKempeSwap c b a b_col (resp equiv))) →
      Eliminated c b

open Classical

/-- Helper constructor for Eliminated allowing point-wise existence of swap sets. -/
theorem Eliminated.kempe_choice (c : Configuration) (b : BoundaryColoring c) (a b_col : Color)
    (hb : IsValidBoundaryColoring c b) (hne : a ≠ b_col)
    (hSteps : ∀ (equiv : Nat → Nat → Prop), IsPlanarRingPartition c b a b_col equiv →
      ∃ (S : Nat → Bool), IsValidSwapChoice c b a b_col equiv S ∧
        Eliminated c (boundaryKempeSwap c b a b_col S)) :
    Eliminated c b := by
  have hEx : ∀ (equiv : Nat → Nat → Prop), ∃ S : Nat → Bool,
      IsPlanarRingPartition c b a b_col equiv →
        IsValidSwapChoice c b a b_col equiv S ∧
        Eliminated c (boundaryKempeSwap c b a b_col S) := by
    intro equiv
    by_cases hPart : IsPlanarRingPartition c b a b_col equiv
    · rcases hSteps equiv hPart with ⟨S, hSwap, hElim⟩
      exact ⟨S, fun _ => ⟨hSwap, hElim⟩⟩
    · exact ⟨fun _ => false, fun h => False.elim (hPart h)⟩
  have ⟨resp, hResp⟩ := Classical.axiomOfChoice hEx
  exact Eliminated.kempe b a b_col resp hb hne
    (fun equiv he => (hResp equiv he).1)
    (fun equiv he => (hResp equiv he).2)

/-- 
True D-Reducibility (RSST / Gonthier Definition):
A configuration is D-reducible if every valid boundary coloring is eliminated
under the adversarial Kempe game.
-/
def IsDReducible (c : Configuration) : Prop :=
  ∀ (b : BoundaryColoring c), IsValidBoundaryColoring c b → Eliminated c b

/-- 
True C-Reducibility (RSST / Gonthier Definition):
A configuration is C-reducible if it has a non-empty list of contract edges
and every valid boundary coloring that extends to the contracted configuration
is eliminated under the adversarial Kempe game.
-/
def IsCReducible (c : Configuration) : Prop :=
  c.contractEdges ≠ [] ∧
  ∀ (b : BoundaryColoring c), IsValidBoundaryColoring c b → extendsToContracted c b → Eliminated c b

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
    is eliminated under the adversarial Kempe game. -/
theorem reducible_elimination (c : Configuration) (hRed : IsReducible c) :
    ∀ (b : BoundaryColoring c), IsValidBoundaryColoring c b → extendsToContracted c b → Eliminated c b := by
  intro b hb hSat
  cases hRed with
  | inl hD => exact hD b hb
  | inr hC => exact hC.2 b hb hSat

/-- A trivial 1-ring configuration with empty interior. -/
def ring1Config : Configuration := {
  ringSize := 1,
  interiorSize := 0,
  adj := fun _ _ => false,
  contractEdges := []
}

/-- The 1-ring configuration is D-reducible under the adversarial Eliminated definition. -/
theorem ring1Config_is_d_reducible : IsDReducible ring1Config := by
  intro b _
  apply Eliminated.ext
  refine ⟨fun _ => b 0, ?_, ?_⟩
  · intro i hi
    dsimp [ring1Config] at hi
    have : i = 0 := by omega
    subst this; rfl
  · intro i j _ _ hadj
    dsimp [ring1Config] at hadj
    contradiction

/-- Sanity check: IsReducible is non-vacuous and inhabited by explicit configurations. -/
theorem ring1Config_is_reducible : IsReducible ring1Config :=
  Or.inl ring1Config_is_d_reducible

end Math
