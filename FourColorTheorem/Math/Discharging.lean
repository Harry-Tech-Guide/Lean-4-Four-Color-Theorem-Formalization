import FourColorTheorem.Math.Reducibility
import FourColorTheorem.Math.Planar

namespace Math

/-- The unavoidable set of configurations for the Four Color Theorem.
In the actual Appel-Haken/Gonthier proof, this is a specific list of 633 configurations. -/
axiom unavoidableSet : List Configuration

/-- A configuration `c` appears in a hypermap `H` if `c` is isomorphic to a subgraph of `H`. -/
axiom appearsIn {D : Type} (c : Configuration) (H : Hypermap D) : Prop

/-- The Unavoidability Theorem (Discharging Method):
Every connected, planar combinatorial map contains at least one configuration
from the unavoidable set. 
In the formal proof, this is established by assigning an initial "charge" to each node and face
based on Euler's formula, and then applying a set of discharging rules that move charge around.
Since the total charge is positive, some local configuration must end up with a positive charge,
forcing it to be one of the unavoidable configurations. -/
axiom unavoidability_theorem {D : Type} (H : Hypermap D) [CombinatorialMap H] (h : H.isPlanar) :
  ∃ (c : Configuration), c ∈ unavoidableSet ∧ appearsIn c H

/-- The Reducibility Theorem:
Every configuration in the unavoidable set is reducible (either D-reducible or C-reducible).
Unlike unavoidability, which is a structural proof, this theorem is proven computationally.
A verified algorithm runs on all 633 configurations and outputs `true`. -/
axiom reducibility_theorem :
  ∀ (c : Configuration), c ∈ unavoidableSet → IsReducible c

end Math
