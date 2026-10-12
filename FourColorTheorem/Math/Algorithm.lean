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
    - rank > 0 colorings admit a valid boundary Kempe swap to a coloring of strictly smaller rank. -/
structure KempeEliminationWitness (c : Configuration) where
  rank : BoundaryColoring c → Nat
  base_case : ∀ b, IsValidBoundaryColoring c b → rank b = 0 → extendsToInterior c b
  step_case : ∀ b, IsValidBoundaryColoring c b → rank b > 0 →
    ∃ b', IsValidBoundaryColoring c b' ∧ kempeEquivalent c b b' ∧ rank b' < rank b

/-- Fundamental Reducibility Induction Theorem:
    Every configuration equipped with a Kempe elimination witness is mathematically D-reducible.
    Proved by well-founded induction on the elimination rank. -/
theorem dreducible_of_elimination_witness (c : Configuration) (w : KempeEliminationWitness c) :
    IsDReducible c := by
  intro b hb
  have h_ind : ∀ n, ∀ b, IsValidBoundaryColoring c b → w.rank b ≤ n →
      (extendsToInterior c b ∨ ∃ b', IsValidBoundaryColoring c b' ∧ kempeEquivalent c b b' ∧ extendsToInterior c b') := by
    intro n
    induction n with
    | zero =>
      intro b hb hle
      have hr0 : w.rank b = 0 := Nat.le_zero.mp hle
      exact Or.inl (w.base_case b hb hr0)
    | succ n ih =>
      intro b hb hle
      by_cases hr0 : w.rank b = 0
      · exact Or.inl (w.base_case b hb hr0)
      · have hpos : w.rank b > 0 := Nat.pos_of_ne_zero hr0
        rcases w.step_case b hb hpos with ⟨b', hb', hEquiv, hlt⟩
        have hle' : w.rank b' ≤ n := Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hlt hle)
        have ih_b' := ih b' hb' hle'
        cases ih_b' with
        | inl hExt' =>
          exact Or.inr ⟨b', hb', hEquiv, hExt'⟩
        | inr hTrans =>
          rcases hTrans with ⟨b'', hb'', hEquiv'', hExt''⟩
          have hEquivTotal := KempeEquivalent.trans hEquiv hEquiv''
          exact Or.inr ⟨b'', hb'', hEquivTotal, hExt''⟩
  exact h_ind (w.rank b) b hb (Nat.le_refl _)

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

/-- Elimination Witness Synthesis Theorem:
    Any mathematically D-reducible configuration constructively admits a canonical
    Kempe elimination witness of rank ≤ 1. -/
noncomputable def elimination_witness_of_dreducible (c : Configuration) (h : IsDReducible c) :
    KempeEliminationWitness c :=
  let rank : BoundaryColoring c → Nat := fun b => if extendsToInterior c b then 0 else 1
  { rank := rank,
    base_case := by
      intro b _ hr0
      dsimp [rank] at hr0
      split at hr0
      · rename_i hExt; exact hExt
      · contradiction,
    step_case := by
      intro b hb _
      have hCases := h b hb
      cases hCases with
      | inl hExt =>
        -- rank b = 0, but premise had rank b > 0
        dsimp [rank]
        have hr0 : (if extendsToInterior c b then 0 else 1) = 0 := if_pos hExt
        -- impossible since rank b > 0
        intro hpos
        omega
      | inr hKempe =>
        intro _
        rcases hKempe with ⟨b', hb', hEquiv, hExt'⟩
        refine ⟨b', hb', hEquiv, ?_⟩
        dsimp [rank]
        have hr' : (if extendsToInterior c b' then 0 else 1) = 0 := if_pos hExt'
        have hnotExt : ¬ extendsToInterior c b := by
          intro hExt
          have hr0 : (if extendsToInterior c b then 0 else 1) = 0 := if_pos hExt
          rename_i hpos
          omega
        have hrb : (if extendsToInterior c b then 0 else 1) = 1 := if_neg hnotExt
        rw [hr', hrb]
        exact Nat.zero_lt_one }

/-- Exact Mathematical Equivalence between D-Reducibility and Kempe Elimination Witness. -/
theorem dreducible_iff_elimination_witness (c : Configuration) :
    IsDReducible c ↔ Nonempty (KempeEliminationWitness c) :=
  ⟨fun h => ⟨elimination_witness_of_dreducible c h⟩,
   fun ⟨w⟩ => dreducible_of_elimination_witness c w⟩

end Math
