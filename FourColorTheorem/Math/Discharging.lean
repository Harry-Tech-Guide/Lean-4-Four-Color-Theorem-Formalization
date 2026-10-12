import FourColorTheorem.Math.HypermapGraph

namespace Math

namespace Hypermap

variable (H : Hypermap) [DecidableEq H.Dart]

/-- The degree of a node is the length of its orbit under the `node` permutation. -/
def nodeDegree (d : H.Dart) (fuel : Nat := 1000) : Nat :=
  (getOrbit H.node fuel d).length

/-- The degree of a face is the length of its orbit under the `face` permutation. -/
def faceDegree (d : H.Dart) (fuel : Nat := 1000) : Nat :=
  (getOrbit H.face fuel d).length

end Hypermap

namespace Discharging

variable (H : Hypermap) [DecidableEq H.Dart]

/-- The fundamental principle of the Discharging Method.
By Euler's formula, in a maximal planar graph (where every face is a triangle),
the sum of (6 - degree(v)) over all vertices is exactly 12.
To avoid rational numbers, we multiply the charge by 10.
Initial charge = 10 * (6 - degree(v)) -/
def initialCharge (v : H.Dart) (fuel : Nat := 1000) : Int :=
  10 * (6 - (Hypermap.nodeDegree H v fuel : Int))

/-- A total charge function over the hypermap. 
We only sum over canonical darts (one per vertex) to avoid double counting. -/
def totalInitialCharge (darts : List H.Dart) : Int :=
  let G := Hypermap.extractGraph H darts
  let rec sum (vs : List H.Dart) (acc : Int) :=
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

theorem shift_self_zero {D : Type} (rule : ChargeShift D) (x : D) : rule.shift x x = 0 := by
  have h := rule.conservation x x
  omega

def sumShiftsTo {D : Type} (rule : ChargeShift D) (v : D) : List D → Int
  | [] => 0
  | t :: ts => rule.shift v t + sumShiftsTo rule v ts

def sumOppositeShifts {D : Type} (rule : ChargeShift D) (v : D) : List D → Int
  | [] => 0
  | s :: ss => rule.shift s v + sumOppositeShifts rule v ss

def totalShifts {D : Type} (rule : ChargeShift D) (sources targets : List D) : Int :=
  match sources with
  | [] => 0
  | s :: ss => sumShiftsTo rule s targets + totalShifts rule ss targets

theorem totalShifts_cons_target {D : Type} (rule : ChargeShift D) (sources : List D) (t : D) (ts : List D) :
    totalShifts rule sources (t :: ts) =
      sumOppositeShifts rule t sources + totalShifts rule sources ts := by
  induction sources with
  | nil => rfl
  | cons s ss ih =>
    dsimp [totalShifts, sumShiftsTo, sumOppositeShifts]
    rw [ih]
    omega

theorem sumShiftsTo_plus_opposite {D : Type} (rule : ChargeShift D) (v : D) (vs : List D) :
    sumShiftsTo rule v vs + sumOppositeShifts rule v vs = 0 := by
  induction vs with
  | nil => rfl
  | cons t ts ih =>
    dsimp [sumShiftsTo, sumOppositeShifts]
    have hcons := rule.conservation v t
    omega

theorem totalShifts_cons_self {D : Type} (rule : ChargeShift D) (v : D) (vs : List D) :
    totalShifts rule (v :: vs) (v :: vs) =
      rule.shift v v +
      (sumShiftsTo rule v vs + sumOppositeShifts rule v vs) +
      totalShifts rule vs vs := by
  dsimp [totalShifts]
  rw [totalShifts_cons_target]
  dsimp [sumShiftsTo, sumOppositeShifts]
  omega

/-- Charge Conservation Theorem:
    The sum of all charge shifts over any finite list of vertices is identically zero. -/
theorem totalShifts_self_zero {D : Type} (rule : ChargeShift D) (vs : List D) :
    totalShifts rule vs vs = 0 := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    rw [totalShifts_cons_self]
    rw [shift_self_zero]
    rw [sumShiftsTo_plus_opposite]
    rw [ih]
    rfl

/-- The final charge of a vertex after applying a set of discharging rules.
    Defined as the initial charge plus all net shifts received from adjacent vertices. -/
def finalCharge (rule : ChargeShift H.Dart) (darts : List H.Dart) (v : H.Dart) : Int :=
  let G := Hypermap.extractGraph H darts
  initialCharge H v + sumShiftsTo rule v G.vertices

def sumCharges {D : Type} (f : D → Int) : List D → Int
  | [] => 0
  | v :: vs => f v + sumCharges f vs

/-- The sum of final charges over any vertex list is the sum of initial charges plus total shifts. -/
theorem sumCharges_finalCharge (rule : ChargeShift H.Dart) (darts : List H.Dart) (vs : List H.Dart) :
    sumCharges (finalCharge H rule darts) vs =
      sumCharges (initialCharge H) vs + totalShifts rule vs (Hypermap.extractGraph H darts).vertices := by
  induction vs with
  | nil => rfl
  | cons v rest ih =>
    simp only [sumCharges, finalCharge, totalShifts]
    omega

/-- Master Discharging Conservation Theorem:
    The sum of final charges across all vertices of the graph equals the sum of initial charges!
    Proved from the global charge conservation theorem `totalShifts_self_zero`. -/
theorem sumCharges_finalCharge_all (rule : ChargeShift H.Dart) (darts : List H.Dart) :
    sumCharges (finalCharge H rule darts) (Hypermap.extractGraph H darts).vertices =
      sumCharges (initialCharge H) (Hypermap.extractGraph H darts).vertices := by
  have h := sumCharges_finalCharge H rule darts (Hypermap.extractGraph H darts).vertices
  rw [totalShifts_self_zero] at h
  omega

/-- Total Final Charge Conservation from Euler Characteristic:
    If the initial Euler charge sums to 120, then the sum of final charges is unconditionally 120! -/
theorem sumCharges_finalCharge_eq_120 (rule : ChargeShift H.Dart) (darts : List H.Dart)
    (hInitial : sumCharges (initialCharge H) (Hypermap.extractGraph H darts).vertices = 120) :
    sumCharges (finalCharge H rule darts) (Hypermap.extractGraph H darts).vertices = 120 := by
  rw [sumCharges_finalCharge_all]
  exact hInitial

theorem sumCharges_nonpos {D : Type} (f : D → Int) (vs : List D)
    (h : ∀ v ∈ vs, f v ≤ 0) : sumCharges f vs ≤ 0 := by
  induction vs with
  | nil =>
    dsimp [sumCharges]
    omega
  | cons v vs ih =>
    dsimp [sumCharges]
    have hv : f v ≤ 0 := h v (List.Mem.head vs)
    have hvs : sumCharges f vs ≤ 0 := ih (fun x hx => h x (List.Mem.tail v hx))
    omega

theorem positive_charge_contradiction {D : Type} (f : D → Int) (vs : List D)
    (hSum : sumCharges f vs = 120) (hNonpos : ∀ v ∈ vs, f v ≤ 0) : False := by
  have hLe := sumCharges_nonpos f vs hNonpos
  omega

/-- Unavoidability Theorem State:
If a discharging rule exists such that the final charge of EVERY vertex is non-positive,
then the sum of final charges is non-positive. 
But Euler's formula says the total initial charge is 120 (12 * 10). 
Since charge is conserved, the total final charge must be 120.
120 <= 0 is a contradiction! 
Therefore, such a graph cannot exist. 
If we define the rules so they only work when a graph DOES NOT contain a reducible configuration,
this contradiction proves the unavoidable set must be present! -/
def UnavoidableSetExists (rule : ChargeShift H.Dart) (darts : List H.Dart) : Prop :=
  (∀ v ∈ (Hypermap.extractGraph H darts).vertices, finalCharge H rule darts v ≤ 0) → False

/-- If the sum of final charges across vertices is 120 (conserved from Euler's characteristic),
    then an unavoidable configuration must exist! -/
theorem unavoidable_set_exists_of_sum_120 (rule : ChargeShift H.Dart) (darts : List H.Dart)
    (hSum : sumCharges (finalCharge H rule darts) (Hypermap.extractGraph H darts).vertices = 120) :
    UnavoidableSetExists H rule darts :=
  fun hNonpos => positive_charge_contradiction (finalCharge H rule darts) _ hSum hNonpos

end Discharging
end Math
