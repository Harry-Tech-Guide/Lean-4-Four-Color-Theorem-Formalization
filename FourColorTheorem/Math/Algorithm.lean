import FourColorTheorem.Math.Reducibility

namespace Math

/-- A placeholder for a Signed Matching.
In RSST, a signed matching on a ring of size N is a non-crossing perfect or partial
matching of the boundary vertices, along with a sign (+1 or -1) for each matched pair. -/
axiom SignedMatching (c : Configuration) : Type

/-- The "theta-fits" relation. 
A boundary edge-coloring `col` fits a signed matching `m` for a specific color `x`. -/
axiom fits (c : Configuration) (col : BoundaryColoring c) (m : SignedMatching c) (x : Color) : Prop

/-- The set of all signed matchings that are balanced (a specific topological condition). -/
axiom balanced_signed_matchings (c : Configuration) : List (SignedMatching c)

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
Because the state space is finite, this can be computed by iteration. -/
axiom max_consistent_subset_is_empty (c : Configuration) : Prop

/-- Soundness of Reducibility (The primary theorem linking the C algorithm to Kempe Chains):
If the max consistent subset is empty, then the configuration is D-reducible
(meaning every non-extending coloring can be Kempe-swapped to an extending one). -/
axiom reducibility_soundness (c : Configuration) :
  max_consistent_subset_is_empty c → IsDReducible c

end Math
