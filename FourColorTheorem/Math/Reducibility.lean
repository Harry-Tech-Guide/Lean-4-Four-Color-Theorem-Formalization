import FourColorTheorem.Math.Kempe

namespace Math

/-- A Configuration represents a specific patch of regions.
For computational reducibility checking, we define it by its boundary size,
its interior size, and an adjacency matrix for all nodes.
Nodes `0` to `ringSize - 1` are on the boundary.
Nodes `ringSize` to `ringSize + interiorSize - 1` are in the interior. -/
structure Configuration where
  ringSize : Nat
  interiorSize : Nat
  adj : Nat → Nat → Bool

/-- The total number of nodes in the configuration. -/
def Configuration.totalNodes (c : Configuration) := c.ringSize + c.interiorSize

/-- A valid full coloring of the configuration. -/
def IsValidConfigColoring (c : Configuration) (color : Nat → Color) : Prop :=
  ∀ i j, i < c.totalNodes → j < c.totalNodes → c.adj i j = true → color i ≠ color j

/-- A boundary coloring is just a coloring of the nodes `0` to `ringSize - 1`. -/
def BoundaryColoring (c : Configuration) := Nat → Color

/-- A boundary coloring is valid if adjacent nodes on the boundary have different colors. -/
def IsValidBoundaryColoring (c : Configuration) (b : BoundaryColoring c) : Prop :=
  ∀ i j, i < c.ringSize → j < c.ringSize → c.adj i j = true → b i ≠ b j

/-- A boundary coloring extends to the interior if there exists a full coloring
that matches the boundary coloring on the boundary nodes. -/
def extendsToInterior (c : Configuration) (b : BoundaryColoring c) : Prop :=
  ∃ (full : Nat → Color),
    (∀ i, i < c.ringSize → full i = b i) ∧
    IsValidConfigColoring c full

/-- D-Reducibility:
A configuration is D-reducible if EVERY valid boundary coloring can be directly
extended to color the interior. -/
def IsDReducible (c : Configuration) : Prop :=
  ∀ (b : BoundaryColoring c), IsValidBoundaryColoring c b → extendsToInterior c b

/-- C-Reducibility (Placeholder) -/
axiom kempeEquivalent (c : Configuration) (b1 b2 : BoundaryColoring c) : Prop

def IsCReducible (c : Configuration) : Prop :=
  ∀ (b : BoundaryColoring c), IsValidBoundaryColoring c b → ¬ extendsToInterior c b →
    ∃ (b' : BoundaryColoring c), IsValidBoundaryColoring c b' ∧ kempeEquivalent c b b' ∧ extendsToInterior c b'

def IsReducible (c : Configuration) : Prop :=
  IsDReducible c ∨ IsCReducible c

end Math
