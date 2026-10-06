
import FourColorTheorem.Math.KempeConsistency

-- Step 10: Combinatorial Planarity (Non-Crossing Matchings)

namespace Hypermap

/-- A boolean relation representing the equivalence classes of a partial matching.
    Two vertices are equivalent if they are the exact same vertex, 
    or if they are explicitly paired together in the matching array. -/
def MatchingEquiv (m : Array (Nat × Nat)) (k : Nat) (i j : Fin k) : Prop :=
  i = j ∨ (i.val, j.val) ∈ m.toList ∨ (j.val, i.val) ∈ m.toList

/-- A matching is strictly non-crossing if it never contains two pairs (i, l) and (j, p)
    such that their intervals overlap (i < j < l < p). -/
def IsNonCrossing (m : Array (Nat × Nat)) : Prop :=
  ∀ i j l p, i < j → j < l → l < p → 
    ((i, l) ∈ m.toList ∨ (l, i) ∈ m.toList) → 
    ((j, p) ∈ m.toList ∨ (p, j) ∈ m.toList) → 
    False

/-- Theorem: If a matching array is strictly non-crossing, then the resulting 
    equivalence relation trivially perfectly satisfies the planar non-crossing 
    topological axioms of Kempe chains. -/
theorem matching_satisfies_planarity (m : Array (Nat × Nat)) (k : Nat) (hNC : IsNonCrossing m) :
  ∀ i j l p : Fin k, i.val < j.val → j.val < l.val → l.val < p.val → 
    MatchingEquiv m k i l → MatchingEquiv m k j p → MatchingEquiv m k i j := by
  intro i j l p h1 h2 h3 h_il h_jp
  -- Since i < j < l < p, they are all distinct.
  -- Thus h_il means they are paired, and h_jp means they are paired.
  have h_il_pair : (i.val, l.val) ∈ m.toList ∨ (l.val, i.val) ∈ m.toList := by
    dsimp [MatchingEquiv] at h_il
    rcases h_il with h_eq | h_in | h_rev
    · -- i = l contradicts i < l
      have : i.val < l.val := Nat.lt_trans h1 h2
      rw [h_eq] at this
      exact False.elim (Nat.lt_irrefl l.val this)
    · exact Or.inl h_in
    · exact Or.inr h_rev

  have h_jp_pair : (j.val, p.val) ∈ m.toList ∨ (p.val, j.val) ∈ m.toList := by
    dsimp [MatchingEquiv] at h_jp
    rcases h_jp with h_eq | h_in | h_rev
    · -- j = p contradicts j < p
      have : j.val < p.val := Nat.lt_trans h2 h3
      rw [h_eq] at this
      exact False.elim (Nat.lt_irrefl p.val this)
    · exact Or.inl h_in
    · exact Or.inr h_rev

  -- This immediately triggers the IsNonCrossing contradiction!
  have contra := hNC i.val j.val l.val p.val h1 h2 h3 h_il_pair h_jp_pair
  exact False.elim contra

end Hypermap
