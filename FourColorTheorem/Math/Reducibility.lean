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

/-- A pairing θ = {{a,b}, {c,d}} of the four distinct colors. -/
structure ColorPairing where
  a : Color
  b : Color
  c : Color
  d : Color
  distinct : a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d
  deriving DecidableEq

/-- Kempe swap function induced by a color pairing θ:
    swaps a ↔ b on {a, b} and swaps c ↔ d on {c, d}. -/
def ColorPairing.swap (θ : ColorPairing) (col : Color) : Color :=
  if col = θ.a then θ.b
  else if col = θ.b then θ.a
  else if col = θ.c then θ.d
  else if col = θ.d then θ.c
  else col

theorem ColorPairing.swap_inv (θ : ColorPairing) (col : Color) :
    θ.swap (θ.swap col) = col := by
  rcases θ with ⟨a, b, c, d, h⟩
  cases col <;> cases a <;> cases b <;> cases c <;> cases d <;> revert h <;> decide

theorem ColorPairing.swap_inj (θ : ColorPairing) (col1 col2 : Color)
    (h : θ.swap col1 = θ.swap col2) : col1 = col2 := by
  have := congrArg θ.swap h
  rw [θ.swap_inv, θ.swap_inv] at this
  exact this

theorem ColorPairing.swap_mem_ab (θ : ColorPairing) (col : Color) :
    (θ.swap col = θ.a ∨ θ.swap col = θ.b) ↔ (col = θ.a ∨ col = θ.b) := by
  rcases θ with ⟨a, b, c, d, h⟩
  cases col <;> cases a <;> cases b <;> cases c <;> cases d <;> revert h <;> decide

theorem ColorPairing.swap_mem_cd (θ : ColorPairing) (col : Color) :
    (θ.swap col = θ.c ∨ θ.swap col = θ.d) ↔ (col = θ.c ∨ col = θ.d) := by
  rcases θ with ⟨a, b, c, d, h⟩
  cases col <;> cases a <;> cases b <;> cases c <;> cases d <;> revert h <;> decide

theorem ColorPairing.mem_all (θ : ColorPairing) (col : Color) :
    col = θ.a ∨ col = θ.b ∨ col = θ.c ∨ col = θ.d := by
  rcases θ with ⟨a, b, c, d, h⟩
  cases col <;> cases a <;> cases b <;> cases c <;> cases d <;> revert h <;> decide

/-- A boundary Kempe swap on a subset S of ring vertices under color pairing θ:
    swaps a ↔ b on the chosen ab-classes and c ↔ d on the chosen cd-classes. -/
def boundaryKempeSwap (_ : Configuration) (b : Nat → Color) (θ : ColorPairing) (S : Nat → Bool) : Nat → Color :=
  fun i => if S i then θ.swap (b i) else b i

/-- Swapping twice with the same boundary Kempe swap is the identity. -/
theorem boundaryKempeSwap_inv (c : Configuration) (b : BoundaryColoring c) (θ : ColorPairing) (S : Nat → Bool) :
    boundaryKempeSwap c (boundaryKempeSwap c b θ S) θ S = b := by
  funext i
  dsimp [boundaryKempeSwap]
  split
  · exact θ.swap_inv (b i)
  · rfl

/-- Helper lemma: boundary Kempe swap preserves membership in {a, b}. -/
theorem boundaryKempeSwap_ab_mem (c : Configuration) (b : BoundaryColoring c) (θ : ColorPairing) (S : Nat → Bool)
    (i : Nat) :
    (boundaryKempeSwap c b θ S i = θ.a ∨ boundaryKempeSwap c b θ S i = θ.b) ↔ (b i = θ.a ∨ b i = θ.b) := by
  dsimp [boundaryKempeSwap]
  split
  · exact θ.swap_mem_ab (b i)
  · rfl

/-- Helper lemma: boundary Kempe swap preserves membership in {c, d}. -/
theorem boundaryKempeSwap_cd_mem (c : Configuration) (b : BoundaryColoring c) (θ : ColorPairing) (S : Nat → Bool)
    (i : Nat) :
    (boundaryKempeSwap c b θ S i = θ.c ∨ boundaryKempeSwap c b θ S i = θ.d) ↔ (b i = θ.c ∨ b i = θ.d) := by
  dsimp [boundaryKempeSwap]
  split
  · exact θ.swap_mem_cd (b i)
  · rfl

/-- A configuration has a chordless ring boundary if the only edges between ring vertices are the cycle edges. -/
def IsChordlessRing (c : Configuration) : Prop :=
  ∀ i < c.ringSize, ∀ j < c.ringSize,
    c.adj i j = true → (j = (i + 1) % c.ringSize ∨ i = (j + 1) % c.ringSize)

/-- A joint planar ring partition for boundary coloring b and pairing θ = {{a,b}, {c,d}}:
    1. π_ab is an equivalence relation on ring vertices colored a or b.
    2. π_cd is an equivalence relation on ring vertices colored c or d.
    3. Ring-adjacent vertices colored in the same pair are related in the respective partition.
    4. Non-crossing planarity:
       - No two classes of π_ab cross each other.
       - No two classes of π_cd cross each other.
       - No class of π_ab crosses any class of π_cd. -/
structure IsJointPlanarRingPartition (c : Configuration) (b : BoundaryColoring c) (θ : ColorPairing)
    (equiv_ab equiv_cd : Nat → Nat → Prop) : Prop where
  ab_refl : ∀ i < c.ringSize, (b i = θ.a ∨ b i = θ.b) → equiv_ab i i
  ab_symm : ∀ i < c.ringSize, ∀ j < c.ringSize, equiv_ab i j → equiv_ab j i
  ab_trans : ∀ i < c.ringSize, ∀ j < c.ringSize, ∀ l < c.ringSize, equiv_ab i j → equiv_ab j l → equiv_ab i l
  ab_color : ∀ i < c.ringSize, ∀ j < c.ringSize, equiv_ab i j → (b i = θ.a ∨ b i = θ.b)
  cd_refl : ∀ i < c.ringSize, (b i = θ.c ∨ b i = θ.d) → equiv_cd i i
  cd_symm : ∀ i < c.ringSize, ∀ j < c.ringSize, equiv_cd i j → equiv_cd j i
  cd_trans : ∀ i < c.ringSize, ∀ j < c.ringSize, ∀ l < c.ringSize, equiv_cd i j → equiv_cd j l → equiv_cd i l
  cd_color : ∀ i < c.ringSize, ∀ j < c.ringSize, equiv_cd i j → (b i = θ.c ∨ b i = θ.d)
  ab_adj : ∀ i < c.ringSize, ∀ j < c.ringSize, c.adj i j = true →
    (b i = θ.a ∨ b i = θ.b) → (b j = θ.a ∨ b j = θ.b) → equiv_ab i j
  cd_adj : ∀ i < c.ringSize, ∀ j < c.ringSize, c.adj i j = true →
    (b i = θ.c ∨ b i = θ.d) → (b j = θ.c ∨ b j = θ.d) → equiv_cd i j
  ab_noncross : ∀ i j l m, i < j → j < l → l < m → m < c.ringSize →
    equiv_ab i l → equiv_ab j m → equiv_ab i j
  cd_noncross : ∀ i j l m, i < j → j < l → l < m → m < c.ringSize →
    equiv_cd i l → equiv_cd j m → equiv_cd i j
  cross_ab_cd : ∀ i j l m, i < j → j < l → l < m → m < c.ringSize →
    equiv_ab i l → equiv_cd j m → False
  cross_cd_ab : ∀ i j l m, i < j → j < l → l < m → m < c.ringSize →
    equiv_cd i l → equiv_ab j m → False

/-- A valid swap choice S over a joint planar ring partition:
    1. S only contains ring vertices.
    2. S is a union of equivalence classes of equiv_ab (respects π_ab).
    3. S is a union of equivalence classes of equiv_cd (respects π_cd). -/
structure IsValidSwapChoice (c : Configuration) (b : BoundaryColoring c) (θ : ColorPairing)
    (equiv_ab equiv_cd : Nat → Nat → Prop) (S : Nat → Bool) : Prop where
  ring_only : ∀ i, S i = true → i < c.ringSize
  respects_ab : ∀ i < c.ringSize, ∀ j < c.ringSize, equiv_ab i j → S i = S j
  respects_cd : ∀ i < c.ringSize, ∀ j < c.ringSize, equiv_cd i j → S i = S j

/-- An admissible swap choice over a joint planar partition preserves boundary coloring validity. -/
theorem swap_preserves_valid (c : Configuration) (b : BoundaryColoring c) (θ : ColorPairing)
    (equiv_ab equiv_cd : Nat → Nat → Prop) (S : Nat → Bool)
    (hb : IsValidBoundaryColoring c b)
    (hPart : IsJointPlanarRingPartition c b θ equiv_ab equiv_cd)
    (hSwap : IsValidSwapChoice c b θ equiv_ab equiv_cd S) :
    IsValidBoundaryColoring c (boundaryKempeSwap c b θ S) := by
  intro i j hi hj hadj
  dsimp [boundaryKempeSwap]
  cases hSi : S i <;> cases hSj : S j
  · dsimp
    exact hb i j hi hj hadj
  · dsimp
    intro h_eq
    by_cases h_ab : b i = θ.a ∨ b i = θ.b
    · have h_swapped_ab : θ.swap (b i) = θ.a ∨ θ.swap (b i) = θ.b :=
        (θ.swap_mem_ab (b i)).mpr h_ab
      have h_bj_ab : b j = θ.a ∨ b j = θ.b := by
        have : b j = θ.swap (b i) := by rw [h_eq, θ.swap_inv]
        rw [this]; exact h_swapped_ab
      have h_equiv := hPart.ab_adj i hi j hj hadj h_ab h_bj_ab
      have h_Seq := hSwap.respects_ab i hi j hj h_equiv
      rw [hSi, hSj] at h_Seq
      contradiction
    · have h_cd : b i = θ.c ∨ b i = θ.d := by
        have h_all := θ.mem_all (b i)
        cases h_all with
        | inl h1 => exact False.elim (h_ab (Or.inl h1))
        | inr h2 =>
          cases h2 with
          | inl h3 => exact False.elim (h_ab (Or.inr h3))
          | inr h4 => exact h4
      have h_swapped_cd : θ.swap (b i) = θ.c ∨ θ.swap (b i) = θ.d :=
        (θ.swap_mem_cd (b i)).mpr h_cd
      have h_bj_cd : b j = θ.c ∨ b j = θ.d := by
        have : b j = θ.swap (b i) := by rw [h_eq, θ.swap_inv]
        rw [this]; exact h_swapped_cd
      have h_equiv := hPart.cd_adj i hi j hj hadj h_cd h_bj_cd
      have h_Seq := hSwap.respects_cd i hi j hj h_equiv
      rw [hSi, hSj] at h_Seq
      contradiction
  · dsimp
    intro h_eq
    by_cases h_ab : b j = θ.a ∨ b j = θ.b
    · have h_swapped_ab : θ.swap (b j) = θ.a ∨ θ.swap (b j) = θ.b :=
        (θ.swap_mem_ab (b j)).mpr h_ab
      have h_bi_ab : b i = θ.a ∨ b i = θ.b := by
        have : b i = θ.swap (b j) := by rw [← h_eq, θ.swap_inv]
        rw [this]; exact h_swapped_ab
      have h_equiv := hPart.ab_adj i hi j hj hadj h_bi_ab h_ab
      have h_Seq := hSwap.respects_ab i hi j hj h_equiv
      rw [hSi, hSj] at h_Seq
      contradiction
    · have h_cd : b j = θ.c ∨ b j = θ.d := by
        have h_all := θ.mem_all (b j)
        cases h_all with
        | inl h1 => exact False.elim (h_ab (Or.inl h1))
        | inr h2 =>
          cases h2 with
          | inl h3 => exact False.elim (h_ab (Or.inr h3))
          | inr h4 => exact h4
      have h_swapped_cd : θ.swap (b j) = θ.c ∨ θ.swap (b j) = θ.d :=
        (θ.swap_mem_cd (b j)).mpr h_cd
      have h_bi_cd : b i = θ.c ∨ b i = θ.d := by
        have : b i = θ.swap (b j) := by rw [← h_eq, θ.swap_inv]
        rw [this]; exact h_swapped_cd
      have h_equiv := hPart.cd_adj i hi j hj hadj h_bi_cd h_cd
      have h_Seq := hSwap.respects_cd i hi j hj h_equiv
      rw [hSi, hSj] at h_Seq
      contradiction
  · dsimp
    intro h_eq
    have h_orig := θ.swap_inj _ _ h_eq
    exact hb i j hi hj hadj h_orig

/-- 
Adversarial Kempe Elimination (Gonthier / RSST):
A boundary coloring is eliminated if:
1. It extends directly to the interior, or
2. The reducer can choose a color pairing θ = {{a,b}, {c,d}} such that for EVERY
   joint planar partition (π_ab, π_cd) presented by the exterior graph (the adversary),
   there is a valid swap choice S (a union of components) such that the swapped coloring is eliminated.
-/
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

open Classical

/-- Helper constructor for Eliminated allowing point-wise existence of swap sets. -/
theorem Eliminated.kempe_choice (c : Configuration) (b : BoundaryColoring c) (θ : ColorPairing)
    (hb : IsValidBoundaryColoring c b)
    (hSteps : ∀ (equiv_ab equiv_cd : Nat → Nat → Prop),
      IsJointPlanarRingPartition c b θ equiv_ab equiv_cd →
      ∃ (S : Nat → Bool), IsValidSwapChoice c b θ equiv_ab equiv_cd S ∧
        Eliminated c (boundaryKempeSwap c b θ S)) :
    Eliminated c b := by
  have hEx : ∀ (p : (Nat → Nat → Prop) × (Nat → Nat → Prop)), ∃ S : Nat → Bool,
      IsJointPlanarRingPartition c b θ p.1 p.2 →
        IsValidSwapChoice c b θ p.1 p.2 S ∧
        Eliminated c (boundaryKempeSwap c b θ S) := by
    intro ⟨equiv_ab, equiv_cd⟩
    by_cases hPart : IsJointPlanarRingPartition c b θ equiv_ab equiv_cd
    · rcases hSteps equiv_ab equiv_cd hPart with ⟨S, hSwap, hElim⟩
      exact ⟨S, fun _ => ⟨hSwap, hElim⟩⟩
    · exact ⟨fun _ => false, fun h => False.elim (hPart h)⟩
  have ⟨resp_prod, hResp⟩ := Classical.axiomOfChoice hEx
  let resp (e_ab e_cd : Nat → Nat → Prop) : Nat → Bool := resp_prod (e_ab, e_cd)
  exact Eliminated.kempe b θ resp hb
    (fun e_ab e_cd he => (hResp (e_ab, e_cd) he).1)
    (fun e_ab e_cd he => (hResp (e_ab, e_cd) he).2)

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
