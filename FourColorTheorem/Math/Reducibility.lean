import FourColorTheorem.Math.Kempe

namespace Math

structure Configuration where
  ringSize : Nat
  interiorSize : Nat
  adj : Nat → Nat → Bool

def Configuration.totalNodes (c : Configuration) := c.ringSize + c.interiorSize

instance : Inhabited Configuration where
  default := { ringSize := 0, interiorSize := 0, adj := fun _ _ => false }

def IsValidConfigColoring (c : Configuration) (color : Nat → Color) : Prop :=
  ∀ i j, i < c.totalNodes → j < c.totalNodes → c.adj i j = true → color i ≠ color j

def BoundaryColoring (_ : Configuration) := Nat → Color

def IsValidBoundaryColoring (c : Configuration) (b : BoundaryColoring c) : Prop :=
  ∀ i j, i < c.ringSize → j < c.ringSize → c.adj i j = true → b i ≠ b j

def extendsToInterior (c : Configuration) (b : BoundaryColoring c) : Prop :=
  ∃ (full : Nat → Color),
    (∀ i, i < c.ringSize → full i = b i) ∧
    IsValidConfigColoring c full

/-- 
Kempe Equivalence of Boundary Colorings:
Two boundary colorings `b1` and `b2` are Kempe equivalent if there exists a sequence of
valid Kempe chain swaps on the boundary that transforms `b1` into `b2`.
In RSST terminology, this is governed by "Balanced Signed Matchings".
For our theoretical formalization, we define this as a reachability relation.
-/
axiom kempeEquivalent (c : Configuration) (b1 b2 : BoundaryColoring c) : Prop

/-- 
True D-Reducibility (RSST Definition):
A configuration is D-reducible if the set of boundary colorings that do NOT extend
to the interior can be completely eliminated via Kempe equivalence.
Specifically, for any non-extending boundary coloring, there must be a Kempe-equivalent
boundary coloring that DOES extend.
(Because if it extends, we can color the interior, and if we can color the interior,
we can just apply the Kempe swap on the whole graph to get the original boundary coloring!)
-/
def IsDReducible (c : Configuration) : Prop :=
  ∀ (b : BoundaryColoring c), IsValidBoundaryColoring c b → 
    (extendsToInterior c b ∨ ∃ b', IsValidBoundaryColoring c b' ∧ kempeEquivalent c b b' ∧ extendsToInterior c b')

end Math
