import FourColorTheorem.Math.Reducibility
import FourColorTheorem.Math.ComputableReducer
import FourColorTheorem.Math.TestComputable

namespace Math

/-- A Signed Matching on a ring of size N.
In RSST, a signed matching is a non-crossing perfect or partial
matching of the boundary edges, along with a sign (+1 or -1) for each matched pair. -/
def SignedMatching (_ : Configuration) : Type :=
  ComputableReducer.SignedMatching

/-- The "theta-fits" relation. 
A boundary edge-coloring `col` fits a signed matching `m` for a specific color `x`. -/
def fits (c : Configuration) (col : BoundaryColoring c) (m : SignedMatching c) (x : Color) : Prop :=
  let colList : Array Nat := (Array.range c.ringSize).map (fun i => (col i).toNat)
  let ecol := ComputableReducer.vertexToEdgeColoring c.ringSize colList
  ComputableReducer.checkThetaFit c.ringSize ecol x.toNat m = true

/-- The set of all signed matchings that are balanced (a specific topological condition). -/
def balanced_signed_matchings (c : Configuration) : List (SignedMatching c) :=
  (ComputableReducer.generateBalancedSignedMatchings c.ringSize).toList

/-- The Maximum Consistent Subset Operator.
Given a "live" set of boundary colorings `C`, a signed matching `m` is ALIVE if
EVERY coloring that fits `m` (for any color) is inside `C`.
A coloring `col` in `C` stays ALIVE if for EVERY color `x ∈ {c1, c2, c3}`,
there exists an ALIVE matching `m` such that `col` fits `m` with color `x`. -/
def is_matching_alive (c : Configuration) (live_C : BoundaryColoring c → Prop) (m : SignedMatching c) : Prop :=
  ∀ (col : BoundaryColoring c) (x : Color), fits c col m x → live_C col

def next_live_set (c : Configuration) (live_C : BoundaryColoring c → Prop) (col : BoundaryColoring c) : Prop :=
  live_C col ∧
  ∀ x ∈ [Color.c1, Color.c2, Color.c3], 
    ∃ m ∈ balanced_signed_matchings c, 
      is_matching_alive c live_C m ∧ fits c col m x

/-- A configuration is D-reducible if the greatest fixed point of `next_live_set` 
starting from the set of non-extending colorings is the EMPTY SET. 
Computed concretely by our verified ComputableReducer. -/
def max_consistent_subset_is_empty (c : Configuration) : Prop :=
  ComputableReducer.isComputablyDReducible c = true

/-- Soundness property of Reducibility (linking matching elimination to Kempe Chains):
If the max consistent subset is empty, then the configuration is D-reducible
(meaning every non-extending coloring can be Kempe-swapped to an extending one). -/
def ReducibilitySoundness (c : Configuration) : Prop :=
  max_consistent_subset_is_empty c → IsDReducible c

/-- A Kempe elimination witness for a configuration `c`:
    Assigns each valid boundary coloring a rank `r : Nat` such that:
    - rank 0 colorings extend directly to the interior.
    - rank > 0 colorings admit a color pairing θ such that for every joint planar
      partition (equiv_ab, equiv_cd), there is a valid swap choice S reducing the rank. -/
structure KempeEliminationWitness (c : Configuration) where
  rank : BoundaryColoring c → Nat
  base_case : ∀ b, IsValidBoundaryColoring c b → rank b = 0 → extendsToInterior c b
  step_case : ∀ b, IsValidBoundaryColoring c b → rank b > 0 →
    ∃ (θ : ColorPairing),
      ∀ (equiv_ab equiv_cd : Nat → Nat → Prop), IsJointPlanarRingPartition c b θ equiv_ab equiv_cd →
        ∃ (S : Nat → Bool), IsValidSwapChoice c b θ equiv_ab equiv_cd S ∧
          rank (boundaryKempeSwap c b θ S) < rank b

/-- Fundamental Reducibility Induction Theorem:
    Every configuration equipped with a Kempe elimination witness is mathematically D-reducible.
    Proved by well-founded induction on the elimination rank. -/
theorem dreducible_of_elimination_witness (c : Configuration) (w : KempeEliminationWitness c) :
    IsDReducible c := by
  intro b hb
  have h_ind : ∀ n b, w.rank b ≤ n → IsValidBoundaryColoring c b → Eliminated c b := by
    intro n
    induction n with
    | zero =>
      intro b hle hb
      have hr0 : w.rank b = 0 := Nat.le_zero.mp hle
      exact Eliminated.ext b (w.base_case b hb hr0)
    | succ n ih =>
      intro b hle hb
      by_cases hr0 : w.rank b = 0
      · exact Eliminated.ext b (w.base_case b hb hr0)
      · have hpos : w.rank b > 0 := Nat.pos_of_ne_zero hr0
        rcases w.step_case b hb hpos with ⟨θ, hSteps⟩
        apply Eliminated.kempe_choice c b θ hb
        intro equiv_ab equiv_cd hEquiv
        rcases hSteps equiv_ab equiv_cd hEquiv with ⟨S, hSwap, hlt⟩
        refine ⟨S, hSwap, ?_⟩
        have hle' : w.rank (boundaryKempeSwap c b θ S) ≤ n :=
          Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hle)
        have hValSwapped := swap_preserves_valid c b θ equiv_ab equiv_cd S hb hEquiv hSwap
        exact ih (boundaryKempeSwap c b θ S) hle' hValSwapped
  exact h_ind (w.rank b) b (Nat.le_refl _) hb

/-- Reducibility Soundness Theorem:
    Proven directly by combining an elimination witness with the induction theorem. -/
theorem reducibility_soundness_of_witness (c : Configuration) (w : KempeEliminationWitness c) :
    ReducibilitySoundness c := by
  intro _
  exact dreducible_of_elimination_witness c w

/-- Reducibility Bridge Theorem:
    A configuration whose maximum consistent subset is empty, together with
    reducibility soundness, is mathematically D-reducible. -/
theorem dreducible_of_computable (c : Configuration) 
    (hEmpty : max_consistent_subset_is_empty c) 
    (hSound : ReducibilitySoundness c) : 
    IsDReducible c :=
  hSound hEmpty

/-- The Birkhoff Diamond has an empty maximum consistent subset.
    Proven via computational reflection (`native_decide`) in Lean 4. -/
theorem birkhoff_empty_consistent_subset : max_consistent_subset_is_empty ComputableReducer.birkhoff :=
  ComputableReducer.birkhoff_is_d_reducible

/-- The Birkhoff Diamond is mathematically D-reducible under reducibility soundness. -/
theorem birkhoff_d_reducible (hSound : ReducibilitySoundness ComputableReducer.birkhoff) : 
    IsDReducible ComputableReducer.birkhoff :=
  dreducible_of_computable ComputableReducer.birkhoff birkhoff_empty_consistent_subset hSound

/-- The Birkhoff Diamond is mathematically reducible under reducibility soundness. -/
theorem birkhoff_is_reducible (hSound : ReducibilitySoundness ComputableReducer.birkhoff) : 
    IsReducible ComputableReducer.birkhoff :=
  Or.inl (birkhoff_d_reducible hSound)

end Math
