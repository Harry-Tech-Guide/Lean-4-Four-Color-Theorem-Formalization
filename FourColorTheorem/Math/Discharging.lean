import FourColorTheorem.Math.HypermapGraph

namespace Math

namespace Hypermap

variable {D : Type} (H : Hypermap D)

/-- The degree of a node is the length of its orbit under the `node` permutation. -/
def nodeDegree [DecidableEq D] (d : D) : Nat :=
  (orbit H.node d).length

/-- The degree of a face is the length of its orbit under the `face` permutation. -/
def faceDegree [DecidableEq D] (d : D) : Nat :=
  (orbit H.face d).length

end Hypermap

namespace Discharging

variable {D : Type} [DecidableEq D] (H : Hypermap D)

/-- The fundamental principle of the Discharging Method.
By Euler's formula, in a maximal planar graph (where every face is a triangle),
the sum of (6 - degree(v)) over all vertices is exactly 12.
To avoid rational numbers, we multiply the charge by 10.
Initial charge = 10 * (6 - degree(v)) -/
def initialCharge (v : D) : Int :=
  10 * (6 - (Hypermap.nodeDegree H v : Int))

/-- A total charge function over the hypermap. 
We only sum over canonical darts (one per vertex) to avoid double counting. -/
def totalInitialCharge (darts : List D) : Int :=
  let G := Hypermap.extractGraph H darts
  let rec sum (vs : List D) (acc : Int) :=
    match vs with
    | [] => acc
    | v :: rest => sum rest (acc + initialCharge H v)
  sum G.vertices 0

/-- 
A Discharging Rule specifies how charge is moved from one vertex to another.
In the RSST proof, charge is only moved from vertices of degree 5 to vertices of degree >= 7.
A rule is just a function that dictates how much charge is shifted between two adjacent vertices.
-/
structure ChargeShift (D : Type) where
  /-- Amount of charge to move from `source` to `target`. 
      Uses integer units (1/10th of a base charge). -/
  shift : D → D → Int
  /-- Charge is conserved: no charge is created or destroyed -/
  conservation : ∀ x y, shift x y = - (shift y x)

/-- The final charge of a vertex after applying a set of discharging rules. -/
def finalCharge (rule : ChargeShift D) (darts : List D) (v : D) : Int :=
  let G := Hypermap.extractGraph H darts
  let rec sumShifts (targets : List D) (acc : Int) :=
    match targets with
    | [] => acc
    | t :: rest => sumShifts rest (acc - rule.shift v t)
  -- The final charge is the initial charge PLUS all charge received MINUS all charge sent.
  (initialCharge H v) - sumShifts G.vertices 0

/-- Unavoidability Theorem State:
If a discharging rule exists such that the final charge of EVERY vertex is non-positive,
then the sum of final charges is non-positive. 
But Euler's formula says the total initial charge is 120 (12 * 10). 
Since charge is conserved, the total final charge must be 120.
120 <= 0 is a contradiction! 
Therefore, such a graph cannot exist. 
If we define the rules so they only work when a graph DOES NOT contain a reducible configuration,
this contradiction proves the unavoidable set must be present! -/
def UnavoidableSetExists (rule : ChargeShift D) (darts : List D) : Prop :=
  (∀ v ∈ (Hypermap.extractGraph H darts).vertices, finalCharge H rule darts v ≤ 0) → False

end Discharging
end Math
