import FourColorTheorem.Math.HypermapGraph
import FourColorTheorem.Math.Topology.Euler
import FourColorTheorem.Math.Rules
import FourColorTheorem.Math.Coloring
import FourColorTheorem.Math.TestDischarging

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

/-- Step around a vertex orbit in the rule orientation `inv` (`false` = `node.f`, `true` = `node.inv`). -/
def ruleRot (H : Hypermap) (inv : Bool) (d : H.Dart) : H.Dart :=
  if inv then H.node.inv d else H.node.f d

/-- Step around a vertex orbit opposite to `inv` (`false` = `node.inv`, `true` = `node.f`). -/
def ruleRotInv (H : Hypermap) (inv : Bool) (d : H.Dart) : H.Dart :=
  if inv then H.node.f d else H.node.inv d

/-- Map each RSST rule coordinate `k ∈ {0..16}` around a directed dart `d` to its vertex dart in `H`,
    faithfully matching the 6 cyclic cartwheel neighbor fans constructed by `U` and `V` (`Rules.lean` / `DischargingAlgo.doOutlet`). -/
def ruleVertexDart (H : Hypermap) (inv : Bool) (d : H.Dart) : Nat → H.Dart
  | 0 => d
  | 1 => H.edge.f d
  | 2 => H.edge.f (ruleRot H inv (H.edge.f d))
  | 3 => H.edge.f (ruleRotInv H inv (H.edge.f d))
  | 4 => H.edge.f (ruleRotInv H inv (ruleRotInv H inv d))
  | 5 => H.edge.f (ruleRot H inv (ruleRot H inv d))
  | 6 => H.edge.f (ruleRot H inv (ruleRot H inv (H.edge.f d)))
  | 7 => H.edge.f (ruleRotInv H inv (ruleRotInv H inv (H.edge.f d)))
  | 8 => H.edge.f (ruleRot H inv (ruleRot H inv (H.edge.f (ruleRotInv H inv d))))
  | 9 => H.edge.f (ruleRotInv H inv (ruleRotInv H inv (H.edge.f (ruleRot H inv d))))
  | 10 => H.edge.f (ruleRot H inv (ruleRot H inv (ruleRot H inv (H.edge.f (ruleRotInv H inv d)))))
  | 11 => H.edge.f (ruleRotInv H inv (ruleRotInv H inv (ruleRotInv H inv (H.edge.f (ruleRot H inv d)))))
  | 12 => H.edge.f (ruleRotInv H inv (ruleRotInv H inv (ruleRotInv H inv d)))
  | 13 => H.edge.f (ruleRotInv H inv (ruleRotInv H inv (ruleRotInv H inv (ruleRotInv H inv d))))
  | 14 => H.edge.f (ruleRot H inv (ruleRot H inv (ruleRot H inv d)))
  | 15 => H.edge.f (ruleRot H inv (ruleRot H inv (ruleRot H inv (H.edge.f d))))
  | 16 => H.edge.f (ruleRot H inv (ruleRot H inv (ruleRot H inv (ruleRot H inv (H.edge.f d)))))
  | _ => d

/-- Check whether a vertex degree `deg` satisfies an RSST rule degree bound `(low, upp)`.
    In RSST rule notation (`Rules.lean`), `upp = 12` denotes no upper bound (`∞`),
    and `low = 0` denotes exact degree `upp`. -/
def degMatchesBound (deg : Nat) (bnd : Nat × Nat) : Bool :=
  let upp := if bnd.2 == 9 then 12 else bnd.2
  let low := if bnd.1 == 0 then upp else bnd.1
  decide (low ≤ deg) && (decide (upp == 12) || decide (deg ≤ upp))

/-- Check whether an RSST `RawRule` matches directed dart `d` with reflection orientation `inv`. -/
def matchesRawRule (H : Hypermap) [DecidableEq H.Dart] (fuel : Nat) (inv : Bool) (d : H.Dart) (r : RawRule) : Bool :=
  degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H inv d 0) fuel) r.b0 &&
  degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H inv d 1) fuel) r.b1 &&
  r.triples.all (fun p => degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H inv d p.1) fuel) p.2)

/-- Charge sent by a single RSST `RawRule` (including its reflection if `r.invert = true`) along dart `d`. -/
def rawRuleOutflow (H : Hypermap) [DecidableEq H.Dart] (fuel : Nat) (d : H.Dart) (r : RawRule) : Int :=
  (if matchesRawRule H fuel false d r then 1 else 0) +
  (if r.invert && matchesRawRule H fuel true d r then 1 else 0)

/-- Total charge outflow along directed dart `d` across all 32 RSST rules in `theRules`. -/
def dartRuleOutflow (H : Hypermap) [DecidableEq H.Dart] (fuel : Nat) (d : H.Dart) : Int :=
  theRules.foldl (fun acc r => acc + rawRuleOutflow H fuel d r) 0

/-- Total charge sent from vertex `u` to vertex `v` across all directed darts from `u` to `v`. -/
def vertexRuleOutflow (H : Hypermap) [DecidableEq H.Dart] (fuel : Nat) (u v : H.Dart) : Int :=
  if Hypermap.sameVertex H u v fuel then 0
  else
    ((getOrbit H.node fuel u).filter (fun d => Hypermap.sameVertex H (H.edge.f d) v fuel)).foldl
      (fun acc d => acc + dartRuleOutflow H fuel d) 0

/-- Net RSST charge shift received by `u` from `v`: inflow from `v` to `u` minus outflow from `u` to `v`. -/
def rsstShift (H : Hypermap) [DecidableEq H.Dart] (fuel : Nat := 1000) (u v : H.Dart) : Int :=
  vertexRuleOutflow H fuel v u - vertexRuleOutflow H fuel u v

/-- Skew-symmetry (charge conservation) of the RSST 32-rule charge shift. -/
theorem rsstShift_conservation (H : Hypermap) [DecidableEq H.Dart] (fuel : Nat) (u v : H.Dart) :
    rsstShift H fuel u v = - (rsstShift H fuel v u) := by
  dsimp [rsstShift]
  omega

/-- The canonical RSST 32-rule discharging `ChargeShift` constructed from `theRules` (`Rules.lean`). -/
def rsstChargeShift (H : Hypermap) [DecidableEq H.Dart] (fuel : Nat := 1000) : ChargeShift H.Dart where
  shift := rsstShift H fuel
  conservation := rsstShift_conservation H fuel

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
    Defined as the initial charge (with fuel `darts.length`) plus all net shifts received from adjacent vertices. -/
def finalCharge (rule : ChargeShift H.Dart) (darts : List H.Dart) (v : H.Dart) : Int :=
  let G := Hypermap.extractGraph H darts
  initialCharge H v darts.length + sumShiftsTo rule v G.vertices

def sumCharges {D : Type} (f : D → Int) : List D → Int
  | [] => 0
  | v :: vs => f v + sumCharges f vs

/-- The sum of final charges over any vertex list is the sum of initial charges plus total shifts. -/
theorem sumCharges_finalCharge (rule : ChargeShift H.Dart) (darts : List H.Dart) (vs : List H.Dart) :
    sumCharges (finalCharge H rule darts) vs =
      sumCharges (fun v => initialCharge H v darts.length) vs + totalShifts rule vs (Hypermap.extractGraph H darts).vertices := by
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
      sumCharges (fun v => initialCharge H v darts.length) (Hypermap.extractGraph H darts).vertices := by
  have h := sumCharges_finalCharge H rule darts (Hypermap.extractGraph H darts).vertices
  rw [totalShifts_self_zero] at h
  omega

/-- Total Final Charge Conservation from Euler Characteristic:
    If the initial Euler charge sums to 120, then the sum of final charges is unconditionally 120! -/
theorem sumCharges_finalCharge_eq_120 (rule : ChargeShift H.Dart) (darts : List H.Dart)
    (hInitial : sumCharges (fun v => initialCharge H v darts.length) (Hypermap.extractGraph H darts).vertices = 120) :
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

/-- The sum of integer degrees over a list of vertices. -/
def sumDegrees {D : Type} (deg : D → Int) : List D → Int
  | [] => 0
  | v :: vs => deg v + sumDegrees deg vs

/-- Linear expansion of initial charge sum:
    Sum of initial charges 10 * (6 - deg(v)) expands linearly to 60 * |vs| - 10 * sum(deg(v)). -/
theorem sum_initialCharge_formula (H : Hypermap) [DecidableEq H.Dart] (vs : List H.Dart) (fuel : Nat) :
    sumCharges (fun v => initialCharge H v fuel) vs =
      60 * (vs.length : Int) - 10 * sumDegrees (fun v => (Hypermap.nodeDegree H v fuel : Int)) vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    dsimp only [sumCharges, sumDegrees]
    rw [ih]
    dsimp only [initialCharge]
    have : ((v :: vs).length : Int) = (vs.length : Int) + 1 := by simp
    omega

/-- Initial charge sum derived from Euler's characteristic and maximal planar triangulation:
    When the vertex count is V, edge count is E, face count is F, with degrees summing to 2E,
    Euler's formula V - E + F = 2 and maximal triangulation condition 2E = 3F
    algebraically force the initial charge sum to equal 120. -/
theorem initial_charge_sum_eq_120_of_triangulation (H : Hypermap) [DecidableEq H.Dart]
    (vs : List H.Dart) (fuel : Nat) (E F : Int)
    (hDegSum : sumDegrees (fun v => (Hypermap.nodeDegree H v fuel : Int)) vs = 2 * E)
    (hEuler : (vs.length : Int) - E + F = 2)
    (hTriang : 2 * E = 3 * F) :
    sumCharges (fun v => initialCharge H v fuel) vs = 120 := by
  rw [sum_initialCharge_formula, hDegSum]
  have := Hypermap.euler_initial_charge_sum_eq_120 (vs.length : Int) E F hEuler hTriang
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

/-!
### Stage B.3: Fuel-Independence of Discharging & Unconditional Triangulation Euler-Handshaking Synthesis
-/

/-- Fuel-independence of `Hypermap.nodeDegree` on any complete dart list (`∀ d, d ∈ darts`). -/
theorem nodeDegree_fuel_eq_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    (v : H.Dart) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    Hypermap.nodeDegree H v fuel = Hypermap.nodeDegree H v darts.length := by
  dsimp [Hypermap.nodeDegree]
  rw [Hypermap.getOrbit_fuel_eq_of_complete H.node darts h_all v h_le]

/-- Fuel-independence of `Hypermap.faceDegree` on any complete dart list (`∀ d, d ∈ darts`). -/
theorem faceDegree_fuel_eq_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    (v : H.Dart) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    Hypermap.faceDegree H v fuel = Hypermap.faceDegree H v darts.length := by
  dsimp [Hypermap.faceDegree]
  rw [Hypermap.getOrbit_fuel_eq_of_complete H.face darts h_all v h_le]

/-- Fuel-independence of `Hypermap.sameVertex` on any complete dart list. -/
theorem sameVertex_fuel_eq_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    (u v : H.Dart) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    Hypermap.sameVertex H u v fuel = Hypermap.sameVertex H u v darts.length := by
  dsimp [Hypermap.sameVertex]
  rw [Hypermap.getOrbit_fuel_eq_of_complete H.node darts h_all u h_le]

/-- Fuel-independence of `initialCharge` on any complete dart list. -/
theorem initialCharge_fuel_eq_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    (v : H.Dart) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    initialCharge H v fuel = initialCharge H v darts.length := by
  dsimp [initialCharge]
  rw [nodeDegree_fuel_eq_of_complete H darts h_all v h_le]

/-- Fuel-independence of `matchesRawRule` on any complete dart list. -/
theorem matchesRawRule_fuel_eq_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    (inv : Bool) (d : H.Dart) (r : RawRule) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    matchesRawRule H fuel inv d r = matchesRawRule H darts.length inv d r := by
  dsimp [matchesRawRule]
  rw [nodeDegree_fuel_eq_of_complete H darts h_all (ruleVertexDart H inv d 0) h_le,
      nodeDegree_fuel_eq_of_complete H darts h_all (ruleVertexDart H inv d 1) h_le]
  have h_all_eq :
      (fun p : Nat × (Nat × Nat) => degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H inv d p.1) fuel) p.2) =
      (fun p : Nat × (Nat × Nat) => degMatchesBound (Hypermap.nodeDegree H (ruleVertexDart H inv d p.1) darts.length) p.2) := by
    funext p
    rw [nodeDegree_fuel_eq_of_complete H darts h_all (ruleVertexDart H inv d p.1) h_le]
  rw [h_all_eq]

/-- Fuel-independence of `rawRuleOutflow` on any complete dart list. -/
theorem rawRuleOutflow_fuel_eq_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    (d : H.Dart) (r : RawRule) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    rawRuleOutflow H fuel d r = rawRuleOutflow H darts.length d r := by
  dsimp [rawRuleOutflow]
  rw [matchesRawRule_fuel_eq_of_complete H darts h_all false d r h_le,
      matchesRawRule_fuel_eq_of_complete H darts h_all true d r h_le]

/-- Fuel-independence of `dartRuleOutflow` on any complete dart list. -/
theorem dartRuleOutflow_fuel_eq_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    (d : H.Dart) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    dartRuleOutflow H fuel d = dartRuleOutflow H darts.length d := by
  dsimp [dartRuleOutflow]
  have h_fn :
      (fun (acc : Int) (r : RawRule) => acc + rawRuleOutflow H fuel d r) =
      (fun (acc : Int) (r : RawRule) => acc + rawRuleOutflow H darts.length d r) := by
    funext acc r
    rw [rawRuleOutflow_fuel_eq_of_complete H darts h_all d r h_le]
  rw [h_fn]

/-- Fuel-independence of `vertexRuleOutflow` on any complete dart list. -/
theorem vertexRuleOutflow_fuel_eq_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    (u v : H.Dart) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    vertexRuleOutflow H fuel u v = vertexRuleOutflow H darts.length u v := by
  dsimp [vertexRuleOutflow]
  rw [sameVertex_fuel_eq_of_complete H darts h_all u v h_le,
      Hypermap.getOrbit_fuel_eq_of_complete H.node darts h_all u h_le]
  have h_flt :
      (fun d => Hypermap.sameVertex H (H.edge.f d) v fuel) =
      (fun d => Hypermap.sameVertex H (H.edge.f d) v darts.length) := by
    funext d
    exact sameVertex_fuel_eq_of_complete H darts h_all (H.edge.f d) v h_le
  have h_fold :
      (fun (acc : Int) (d : H.Dart) => acc + dartRuleOutflow H fuel d) =
      (fun (acc : Int) (d : H.Dart) => acc + dartRuleOutflow H darts.length d) := by
    funext acc d
    rw [dartRuleOutflow_fuel_eq_of_complete H darts h_all d h_le]
  rw [h_flt, h_fold]

/-- Fuel-independence of `rsstShift` on any complete dart list. -/
theorem rsstShift_fuel_eq_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    (u v : H.Dart) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    rsstShift H fuel u v = rsstShift H darts.length u v := by
  dsimp [rsstShift]
  rw [vertexRuleOutflow_fuel_eq_of_complete H darts h_all v u h_le,
      vertexRuleOutflow_fuel_eq_of_complete H darts h_all u v h_le]

/-- Fuel-independence of `sumDegrees` on any complete dart list. -/
theorem sumDegrees_fuel_eq_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    (vs : List H.Dart) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    sumDegrees (fun v => (Hypermap.nodeDegree H v fuel : Int)) vs =
      sumDegrees (fun v => (Hypermap.nodeDegree H v darts.length : Int)) vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    dsimp [sumDegrees]
    rw [nodeDegree_fuel_eq_of_complete H darts h_all v h_le, ih]

/-- Equivalence between `sumDegrees` of `nodeDegree` and `Hypermap.sumOrbitLengths H.node`. -/
theorem sumDegrees_nodeDegree_eq_sumOrbitLengths (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (vs : List H.Dart) :
    sumDegrees (fun v => (Hypermap.nodeDegree H v fuel : Int)) vs =
      (Hypermap.sumOrbitLengths H.node fuel vs : Int) := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    dsimp [sumDegrees, Hypermap.sumOrbitLengths]
    rw [ih]
    dsimp [Hypermap.nodeDegree]

/-- Handshaking Lemma for `extractGraph`:
    the sum of vertex degrees over `(extractGraph H darts).vertices` equals `darts.length`
    for any `fuel ≥ darts.length`. -/
theorem sumDegrees_extractGraph_eq_length (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) :
    sumDegrees (fun v => (Hypermap.nodeDegree H v fuel : Int))
      (Hypermap.extractGraph H darts).vertices = (darts.length : Int) := by
  rw [sumDegrees_fuel_eq_of_complete H darts h_all _ h_le]
  rw [sumDegrees_nodeDegree_eq_sumOrbitLengths H darts.length]
  rw [Hypermap.extractGraph_vertices_eq_canonicalOrbits_reverse H darts darts.length]
  rw [Hypermap.sumOrbitLengths_reverse]
  rw [Hypermap.sumOrbitLengths_canonicalOrbits_of_complete H.node darts h_nodup h_all (Nat.le_refl _)]

/-- Handshaking Lemma (`sumDegrees = 2 * E`) for `extractGraph` on any complete, bridgeless hypermap. -/
theorem sumDegrees_extractGraph_eq_two_mul_numEdges (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b : Nat} (h_bridge : Hypermap.isBridgeless H darts fuel_b)
    {fuel_deg fuel : Nat} (h_deg_le : darts.length ≤ fuel_deg) (h_le : darts.length ≤ fuel) :
    sumDegrees (fun v => (Hypermap.nodeDegree H v fuel_deg : Int))
      (Hypermap.extractGraph H darts).vertices = 2 * (Hypermap.numEdges H fuel darts : Int) := by
  rw [sumDegrees_extractGraph_eq_length H darts h_nodup h_all h_deg_le]
  have hE := Hypermap.darts_length_eq_two_mul_numEdges H darts h_nodup h_all h_bridge h_le
  omega

/-- Master Triangulation Euler & Handshaking Package:
    for any complete, bridgeless, connected planar triangulation `(H, darts)`,
    `E = numEdges H fuel darts` and `F = numFaces H fuel darts` satisfy:
    1. `sumDegrees = 2 * E`
    2. `V - E + F = 2`
    3. `2 * E = 3 * F` -/
theorem triangulation_euler_equations_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b : Nat} (h_bridge : Hypermap.isBridgeless H darts fuel_b)
    {fuel_deg fuel : Nat} (h_deg_le : darts.length ≤ fuel_deg) (h_le : darts.length ≤ fuel)
    (h_planar : Hypermap.isPlanar H fuel darts = true)
    (h_conn : Hypermap.numComponents H fuel darts = 1)
    (h_tri : ∀ d ∈ darts, Hypermap.faceDegree H d fuel = 3) :
    ∃ (E F : Int),
      sumDegrees (fun v => (Hypermap.nodeDegree H v fuel_deg : Int))
        (Hypermap.extractGraph H darts).vertices = 2 * E ∧
      ((Hypermap.extractGraph H darts).vertices.length : Int) - E + F = 2 ∧
      2 * E = 3 * F := by
  refine ⟨(Hypermap.numEdges H fuel darts : Int), (Hypermap.numFaces H fuel darts : Int), ?_, ?_, ?_⟩
  · exact sumDegrees_extractGraph_eq_two_mul_numEdges H darts h_nodup h_all h_bridge h_deg_le h_le
  · exact Hypermap.extractGraph_euler_eq_two_of_isPlanar_connected H darts h_all h_le h_planar h_conn
  · exact Hypermap.two_mul_numEdges_eq_three_mul_numFaces_of_triangulation H darts h_nodup h_all h_bridge h_le h_tri

/-- Unconditional Initial Charge Sum = 120 for any complete, bridgeless, connected planar triangulation. -/
theorem initial_charge_sum_eq_120_of_complete_triangulation (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_bridge : Hypermap.isBridgeless H darts)
    (h_planar : Hypermap.isPlanar H darts.length darts = true)
    (h_conn : Hypermap.numComponents H darts.length darts = 1)
    (h_tri : ∀ d ∈ darts, Hypermap.faceDegree H d darts.length = 3) :
    sumCharges (fun v => initialCharge H v darts.length) (Hypermap.extractGraph H darts).vertices = 120 := by
  rcases triangulation_euler_equations_of_complete H darts h_nodup h_all h_bridge
    (Nat.le_refl _) (Nat.le_refl _) h_planar h_conn h_tri with ⟨E, F, hDegSum, hEuler, hTriang⟩
  exact initial_charge_sum_eq_120_of_triangulation H (Hypermap.extractGraph H darts).vertices
    darts.length E F hDegSum hEuler hTriang

/-!
### Stage C.1: Vertex Equivalence (`sameVertex`) & Orbit Degree Invariance
-/

/-- Reflexivity of `Hypermap.sameVertex`. -/
theorem sameVertex_refl (H : Hypermap) [DecidableEq H.Dart] (fuel : Nat) (d : H.Dart) :
    Hypermap.sameVertex H d d fuel = true :=
  Hypermap.getOrbit_contains_self H.node fuel d

/-- Symmetry of `Hypermap.sameVertex` on a complete dart list (`darts.length ≤ fuel`). -/
theorem sameVertex_symm_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u v : H.Dart) :
    Hypermap.sameVertex H u v fuel = Hypermap.sameVertex H v u fuel :=
  Hypermap.getOrbit_contains_symm_of_complete H.node darts h_all h_le u v

/-- Transitivity of `Hypermap.sameVertex` on a complete dart list (`darts.length ≤ fuel`). -/
theorem sameVertex_trans_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u v w : H.Dart}
    (huv : Hypermap.sameVertex H u v fuel = true)
    (hvw : Hypermap.sameVertex H v w fuel = true) :
    Hypermap.sameVertex H u w fuel = true :=
  Hypermap.getOrbit_contains_trans_of_complete H.node darts h_all h_le huv hvw

/-- Every dart `d` in the vertex orbit `getOrbit H.node fuel u` has the same `nodeDegree` as `u`. -/
theorem nodeDegree_eq_of_mem_getOrbit (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u d : H.Dart}
    (h_mem : d ∈ getOrbit H.node fuel u) :
    Hypermap.nodeDegree H d fuel = Hypermap.nodeDegree H u fuel :=
  Hypermap.getOrbit_length_eq_of_complete_mem H.node darts h_all h_le h_mem

/-- Any two darts at the same vertex (`sameVertex H u v fuel = true`) have identical `nodeDegree`. -/
theorem nodeDegree_eq_of_sameVertex (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u v : H.Dart}
    (h_same : Hypermap.sameVertex H u v fuel = true) :
    Hypermap.nodeDegree H v fuel = Hypermap.nodeDegree H u fuel :=
  nodeDegree_eq_of_mem_getOrbit H darts h_all h_le (List.contains_iff_mem.mp h_same)

@[simp] theorem ruleVertexDart_zero (H : Hypermap) (inv : Bool) (d : H.Dart) :
    ruleVertexDart H inv d 0 = d := by
  unfold ruleVertexDart
  rfl

@[simp] theorem ruleVertexDart_one (H : Hypermap) (inv : Bool) (d : H.Dart) :
    ruleVertexDart H inv d 1 = H.edge.f d := by
  unfold ruleVertexDart
  rfl



/-!
### Stage C.2: Additive `foldl` Infrastructure & Structural Degree Bounds on `theRules`
-/

/-- Shift-invariance of integer additive `List.foldl`. -/
theorem foldl_add_shift {α : Type} (L : List α) (f : α → Int) (init : Int) :
    L.foldl (fun acc x => acc + f x) init = init + L.foldl (fun acc x => acc + f x) 0 := by
  induction L generalizing init with
  | nil =>
    dsimp [List.foldl]
    omega
  | cons a as ih =>
    dsimp [List.foldl]
    rw [ih (init + f a), ih (0 + f a)]
    omega

/-- Unfolding integer additive `List.foldl` on `a :: L`. -/
theorem foldl_add_cons {α : Type} (a : α) (L : List α) (f : α → Int) :
    (a :: L).foldl (fun acc x => acc + f x) 0 = f a + L.foldl (fun acc x => acc + f x) 0 := by
  dsimp [List.foldl]
  rw [foldl_add_shift L f (0 + f a)]
  omega

/-- Non-negativity of integer additive `List.foldl` when all terms are non-negative. -/
theorem foldl_add_nonneg {α : Type} (L : List α) (f : α → Int)
    (h_nonneg : ∀ x ∈ L, 0 ≤ f x) :
    0 ≤ L.foldl (fun acc x => acc + f x) 0 := by
  induction L with
  | nil =>
    dsimp [List.foldl]
    omega
  | cons a as ih =>
    rw [foldl_add_cons]
    have ha : 0 ≤ f a := h_nonneg a (List.Mem.head as)
    have has : 0 ≤ as.foldl (fun acc x => acc + f x) 0 :=
      ih (fun x hx => h_nonneg x (List.Mem.tail a hx))
    omega

/-- Vanishing of integer additive `List.foldl` when all terms are zero. -/
theorem foldl_add_eq_zero {α : Type} (L : List α) (f : α → Int)
    (h_zero : ∀ x ∈ L, f x = 0) :
    L.foldl (fun acc x => acc + f x) 0 = 0 := by
  induction L with
  | nil => rfl
  | cons a as ih =>
    rw [foldl_add_cons]
    rw [h_zero a (List.Mem.head as), ih (fun x hx => h_zero x (List.Mem.tail a hx))]
    rfl

/-- Upper bound on integer additive `List.foldl` when each term is bounded above by `c`. -/
theorem foldl_add_le_of_le_const {α : Type} (L : List α) (f : α → Int) (c : Int)
    (h_le : ∀ x ∈ L, f x ≤ c) :
    L.foldl (fun acc x => acc + f x) 0 ≤ c * (L.length : Int) := by
  induction L with
  | nil =>
    dsimp [List.foldl]
    omega
  | cons a as ih =>
    rw [foldl_add_cons]
    have ha : f a ≤ c := h_le a (List.Mem.head as)
    have has : as.foldl (fun acc x => acc + f x) 0 ≤ c * (as.length : Int) :=
      ih (fun x hx => h_le x (List.Mem.tail a hx))
    have hlen : ((a :: as).length : Int) = (as.length : Int) + 1 := by simp
    rw [hlen, Int.mul_add, Int.mul_one]
    omega

/-- Lower bound on integer additive `List.foldl` when each term is bounded below by `c`. -/
theorem foldl_add_ge_of_ge_const {α : Type} (L : List α) (f : α → Int) (c : Int)
    (h_ge : ∀ x ∈ L, c ≤ f x) :
    c * (L.length : Int) ≤ L.foldl (fun acc x => acc + f x) 0 := by
  induction L with
  | nil =>
    dsimp [List.foldl]
    omega
  | cons a as ih =>
    rw [foldl_add_cons]
    have ha : c ≤ f a := h_ge a (List.Mem.head as)
    have has : c * (as.length : Int) ≤ as.foldl (fun acc x => acc + f x) 0 :=
      ih (fun x hx => h_ge x (List.Mem.tail a hx))
    have hlen : ((a :: as).length : Int) = (as.length : Int) + 1 := by simp
    rw [hlen, Int.mul_add, Int.mul_one]
    omega

/-- Every single-rule outflow `rawRuleOutflow` is non-negative (`≥ 0`). -/
theorem rawRuleOutflow_nonneg (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart) (r : RawRule) :
    0 ≤ rawRuleOutflow H fuel d r := by
  dsimp [rawRuleOutflow]
  split <;> split <;> omega

/-- Every single-rule outflow `rawRuleOutflow` is at most `2`. -/
theorem rawRuleOutflow_le_two (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart) (r : RawRule) :
    rawRuleOutflow H fuel d r ≤ 2 := by
  dsimp [rawRuleOutflow]
  split <;> split <;> omega

/-- Total dart outflow `dartRuleOutflow` is non-negative (`≥ 0`). -/
theorem dartRuleOutflow_nonneg (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart) :
    0 ≤ dartRuleOutflow H fuel d := by
  dsimp [dartRuleOutflow]
  exact foldl_add_nonneg theRules (fun r => rawRuleOutflow H fuel d r)
    (fun r _ => rawRuleOutflow_nonneg H fuel d r)

/-- Total vertex-to-vertex outflow `vertexRuleOutflow` is non-negative (`≥ 0`). -/
theorem vertexRuleOutflow_nonneg (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (u v : H.Dart) :
    0 ≤ vertexRuleOutflow H fuel u v := by
  dsimp [vertexRuleOutflow]
  split
  · omega
  · exact foldl_add_nonneg _ (fun d => dartRuleOutflow H fuel d)
      (fun d _ => dartRuleOutflow_nonneg H fuel d)

/-- Decidable source degree bounds for all 35 entries in `theRules`:
    every rule has `5 ≤ r.b0.1 ≤ r.b0.2 ≤ 8`. -/
theorem theRules_b0_bounds :
    ∀ r ∈ theRules, 5 ≤ r.b0.1 ∧ r.b0.1 ≤ r.b0.2 ∧ r.b0.2 ≤ 8 := by decide

/-- Decidable target degree bounds for all 35 entries in `theRules`:
    every rule has `5 ≤ r.b1.1`. -/
theorem theRules_b1_bounds :
    ∀ r ∈ theRules, 5 ≤ r.b1.1 := by decide

/-- Decidable target degree bounds for all rules after Rule 1 (`theRules.tail`):
    every rule in `theRules.tail` has `6 ≤ r.b1.1`. -/
theorem theRules_tail_b1_bounds :
    ∀ r ∈ theRules.tail, 6 ≤ r.b1.1 := by decide

/-- If `0 < bnd.1` and `deg < bnd.1`, then `degMatchesBound deg bnd = false`. -/
theorem degMatchesBound_eq_false_of_lt {deg : Nat} {bnd : Nat × Nat}
    (h_pos : 0 < bnd.1) (h_lt : deg < bnd.1) :
    degMatchesBound deg bnd = false := by
  dsimp [degMatchesBound]
  have h_ne0 : (bnd.1 == 0) = false := beq_eq_false_iff_ne.mpr (by omega)
  rw [h_ne0]
  dsimp
  have h_not_le : ¬ (bnd.1 ≤ deg) := by omega
  rw [decide_eq_false h_not_le]
  rfl

/-- If `bnd.2 ≤ 8` and `bnd.2 < deg`, then `degMatchesBound deg bnd = false`. -/
theorem degMatchesBound_eq_false_of_gt {deg : Nat} {bnd : Nat × Nat}
    (h_upp8 : bnd.2 ≤ 8) (h_gt : bnd.2 < deg) :
    degMatchesBound deg bnd = false := by
  dsimp [degMatchesBound]
  have h_ne9 : (bnd.2 == 9) = false := beq_eq_false_iff_ne.mpr (by omega)
  rw [h_ne9]
  dsimp
  have h_ne12 : ¬ ((bnd.2 == 12) = true) := by
    rw [beq_iff_eq]
    omega
  have h_not_le : ¬ (deg ≤ bnd.2) := by omega
  rw [decide_eq_false h_ne12, decide_eq_false h_not_le]
  simp

/-- If `Hypermap.nodeDegree H d fuel < 5`, no rule in `theRules` matches `d`. -/
theorem matchesRawRule_eq_false_of_deg_lt_5 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (inv : Bool) (d : H.Dart) {r : RawRule} (hr : r ∈ theRules)
    (h_lt : Hypermap.nodeDegree H d fuel < 5) :
    matchesRawRule H fuel inv d r = false := by
  have hb0 := (theRules_b0_bounds r hr).1
  unfold matchesRawRule
  rw [ruleVertexDart_zero, degMatchesBound_eq_false_of_lt (by omega) (by omega)]
  rfl

/-- If `9 ≤ Hypermap.nodeDegree H d fuel`, no rule in `theRules` matches `d`. -/
theorem matchesRawRule_eq_false_of_deg_ge_9 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (inv : Bool) (d : H.Dart) {r : RawRule} (hr : r ∈ theRules)
    (h_ge : 9 ≤ Hypermap.nodeDegree H d fuel) :
    matchesRawRule H fuel inv d r = false := by
  have hb0 := (theRules_b0_bounds r hr).2.2
  unfold matchesRawRule
  rw [ruleVertexDart_zero, degMatchesBound_eq_false_of_gt hb0 (by omega)]
  rfl

/-- If `Hypermap.nodeDegree H (H.edge.f d) fuel < 5`, no rule in `theRules` matches `d`. -/
theorem matchesRawRule_eq_false_of_target_deg_lt_5 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (inv : Bool) (d : H.Dart) {r : RawRule} (hr : r ∈ theRules)
    (h_lt : Hypermap.nodeDegree H (H.edge.f d) fuel < 5) :
    matchesRawRule H fuel inv d r = false := by
  have hb1 := theRules_b1_bounds r hr
  unfold matchesRawRule
  rw [ruleVertexDart_one, @degMatchesBound_eq_false_of_lt (Hypermap.nodeDegree H (H.edge.f d) fuel) r.b1 (by omega) (by omega)]
  simp

/-- If `Hypermap.nodeDegree H (H.edge.f d) fuel ≤ 5`, no rule in `theRules.tail` matches `d`. -/
theorem matchesRawRule_eq_false_of_target_deg_le_5_tail (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (inv : Bool) (d : H.Dart) {r : RawRule} (hr : r ∈ theRules.tail)
    (h_le : Hypermap.nodeDegree H (H.edge.f d) fuel ≤ 5) :
    matchesRawRule H fuel inv d r = false := by
  have hb1 := theRules_tail_b1_bounds r hr
  unfold matchesRawRule
  rw [ruleVertexDart_one, @degMatchesBound_eq_false_of_lt (Hypermap.nodeDegree H (H.edge.f d) fuel) r.b1 (by omega) (by omega)]
  simp


/-- Outflow along dart `d` is `0` when `Hypermap.nodeDegree H d fuel < 5`. -/
theorem dartRuleOutflow_eq_zero_of_deg_lt_5 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart) (h_lt : Hypermap.nodeDegree H d fuel < 5) :
    dartRuleOutflow H fuel d = 0 := by
  dsimp [dartRuleOutflow]
  apply foldl_add_eq_zero
  intro r hr
  dsimp [rawRuleOutflow]
  rw [matchesRawRule_eq_false_of_deg_lt_5 H fuel false d hr h_lt,
      matchesRawRule_eq_false_of_deg_lt_5 H fuel true d hr h_lt]
  simp

/-- Outflow along dart `d` is `0` when `9 ≤ Hypermap.nodeDegree H d fuel`. -/
theorem dartRuleOutflow_eq_zero_of_deg_ge_9 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart) (h_ge : 9 ≤ Hypermap.nodeDegree H d fuel) :
    dartRuleOutflow H fuel d = 0 := by
  dsimp [dartRuleOutflow]
  apply foldl_add_eq_zero
  intro r hr
  dsimp [rawRuleOutflow]
  rw [matchesRawRule_eq_false_of_deg_ge_9 H fuel false d hr h_ge,
      matchesRawRule_eq_false_of_deg_ge_9 H fuel true d hr h_ge]
  simp

/-- Outflow along dart `d` is `0` when target `H.edge.f d` has `nodeDegree < 5`. -/
theorem dartRuleOutflow_eq_zero_of_target_deg_lt_5 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart) (h_lt : Hypermap.nodeDegree H (H.edge.f d) fuel < 5) :
    dartRuleOutflow H fuel d = 0 := by
  dsimp [dartRuleOutflow]
  apply foldl_add_eq_zero
  intro r hr
  dsimp [rawRuleOutflow]
  rw [matchesRawRule_eq_false_of_target_deg_lt_5 H fuel false d hr h_lt,
      matchesRawRule_eq_false_of_target_deg_lt_5 H fuel true d hr h_lt]
  simp

/-- Head-tail decomposition of `dartRuleOutflow` separating Rule 1 (`r₁`) from `theRules.tail`. -/
theorem dartRuleOutflow_eq_rule1_add_tail (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart) :
    dartRuleOutflow H fuel d =
      rawRuleOutflow H fuel d { num := 1, b0 := (5, 5), b1 := (5, 12), triples := [], invert := true } +
      theRules.tail.foldl (fun acc r => acc + rawRuleOutflow H fuel d r) 0 := by
  conv =>
    lhs
    unfold dartRuleOutflow
    change ({ num := 1, b0 := (5, 5), b1 := (5, 12), triples := [], invert := true } :: theRules.tail).foldl
      (fun acc r => acc + rawRuleOutflow H fuel d r) 0
  rw [foldl_add_cons]

/-- Rule 1 outflow is `2` whenever `nodeDegree H d fuel = 5` and `5 ≤ nodeDegree H (H.edge.f d) fuel`. -/
theorem rawRuleOutflow_rule1_eq_two (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_d : Hypermap.nodeDegree H d fuel = 5)
    (h_ed : 5 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    rawRuleOutflow H fuel d { num := 1, b0 := (5, 5), b1 := (5, 12), triples := [], invert := true } = 2 := by
  have h_b0 : degMatchesBound (Hypermap.nodeDegree H d fuel) (5, 5) = true := by
    rw [h_d]; decide
  have h_b1 : degMatchesBound (Hypermap.nodeDegree H (H.edge.f d) fuel) (5, 12) = true := by
    dsimp [degMatchesBound]
    rw [decide_eq_true h_ed]
    rfl
  unfold rawRuleOutflow matchesRawRule
  simp only [ruleVertexDart_zero, ruleVertexDart_one, h_b0, h_b1]
  rfl

/-- Rule 1 outflow is `0` whenever `nodeDegree H d fuel ≠ 5`. -/
theorem rawRuleOutflow_rule1_eq_zero_of_ne_5 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_ne : Hypermap.nodeDegree H d fuel ≠ 5) :
    rawRuleOutflow H fuel d { num := 1, b0 := (5, 5), b1 := (5, 12), triples := [], invert := true } = 0 := by
  have h_b0 : degMatchesBound (Hypermap.nodeDegree H d fuel) (5, 5) = false := by
    rcases Nat.lt_or_gt_of_ne h_ne with h_lt | h_gt
    · exact degMatchesBound_eq_false_of_lt (by decide) h_lt
    · exact degMatchesBound_eq_false_of_gt (by decide) h_gt
  unfold rawRuleOutflow matchesRawRule
  simp only [ruleVertexDart_zero, h_b0]
  rfl


/-- If target `H.edge.f d` has degree `5` and source `d` has degree `≠ 5`, then `dartRuleOutflow H fuel d = 0`. -/
theorem dartRuleOutflow_eq_zero_of_target_deg_5_of_deg_ne_5 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_ed : Hypermap.nodeDegree H (H.edge.f d) fuel = 5)
    (h_ne : Hypermap.nodeDegree H d fuel ≠ 5) :
    dartRuleOutflow H fuel d = 0 := by
  rw [dartRuleOutflow_eq_rule1_add_tail, rawRuleOutflow_rule1_eq_zero_of_ne_5 H fuel d h_ne]
  have h_tail : theRules.tail.foldl (fun acc r => acc + rawRuleOutflow H fuel d r) 0 = 0 := by
    apply foldl_add_eq_zero
    intro r hr
    dsimp [rawRuleOutflow]
    rw [matchesRawRule_eq_false_of_target_deg_le_5_tail H fuel false d hr (by omega),
        matchesRawRule_eq_false_of_target_deg_le_5_tail H fuel true d hr (by omega)]
    simp
  rw [h_tail]
  rfl

/-- If both `d` and `H.edge.f d` have degree `5`, then `dartRuleOutflow H fuel d = 2`. -/
theorem dartRuleOutflow_eq_two_of_deg_5_of_target_deg_5 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_d : Hypermap.nodeDegree H d fuel = 5)
    (h_ed : Hypermap.nodeDegree H (H.edge.f d) fuel = 5) :
    dartRuleOutflow H fuel d = 2 := by
  rw [dartRuleOutflow_eq_rule1_add_tail, rawRuleOutflow_rule1_eq_two H fuel d h_d (by omega)]
  have h_tail : theRules.tail.foldl (fun acc r => acc + rawRuleOutflow H fuel d r) 0 = 0 := by
    apply foldl_add_eq_zero
    intro r hr
    dsimp [rawRuleOutflow]
    rw [matchesRawRule_eq_false_of_target_deg_le_5_tail H fuel false d hr (by omega),
        matchesRawRule_eq_false_of_target_deg_le_5_tail H fuel true d hr (by omega)]
    simp
  rw [h_tail]
  rfl

/-- If `d` has degree `5` and `H.edge.f d` has degree `≥ 5`, then `2 ≤ dartRuleOutflow H fuel d`. -/
theorem two_le_dartRuleOutflow_of_deg_5_of_target_deg_ge_5 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_d : Hypermap.nodeDegree H d fuel = 5)
    (h_ed : 5 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    2 ≤ dartRuleOutflow H fuel d := by
  rw [dartRuleOutflow_eq_rule1_add_tail, rawRuleOutflow_rule1_eq_two H fuel d h_d h_ed]
  have h_tail : 0 ≤ theRules.tail.foldl (fun acc r => acc + rawRuleOutflow H fuel d r) 0 :=
    foldl_add_nonneg theRules.tail (fun r => rawRuleOutflow H fuel d r)
      (fun r _ => rawRuleOutflow_nonneg H fuel d r)
  omega

/-- Vertex outflow `vertexRuleOutflow H fuel u v = 0` when `Hypermap.nodeDegree H u fuel < 5`. -/
theorem vertexRuleOutflow_eq_zero_of_deg_lt_5 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u v : H.Dart)
    (h_lt : Hypermap.nodeDegree H u fuel < 5) :
    vertexRuleOutflow H fuel u v = 0 := by
  dsimp [vertexRuleOutflow]
  split
  · rfl
  · apply foldl_add_eq_zero
    intro d hd
    have hd_orb : d ∈ getOrbit H.node fuel u := (List.mem_filter.mp hd).1
    have hd_deg : Hypermap.nodeDegree H d fuel = Hypermap.nodeDegree H u fuel :=
      nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hd_orb
    exact dartRuleOutflow_eq_zero_of_deg_lt_5 H fuel d (by omega)

/-- Vertex outflow `vertexRuleOutflow H fuel u v = 0` when target `Hypermap.nodeDegree H v fuel < 5`. -/
theorem vertexRuleOutflow_eq_zero_of_target_deg_lt_5 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u v : H.Dart)
    (h_lt : Hypermap.nodeDegree H v fuel < 5) :
    vertexRuleOutflow H fuel u v = 0 := by
  dsimp [vertexRuleOutflow]
  split
  · rfl
  · apply foldl_add_eq_zero
    intro d hd
    have hd_same : Hypermap.sameVertex H (H.edge.f d) v fuel = true := (List.mem_filter.mp hd).2
    have hed_deg : Hypermap.nodeDegree H (H.edge.f d) fuel = Hypermap.nodeDegree H v fuel :=
      (nodeDegree_eq_of_sameVertex H darts h_all h_le hd_same).symm
    exact dartRuleOutflow_eq_zero_of_target_deg_lt_5 H fuel d (by omega)

/-- Net shift `rsstShift H fuel u v = 0` when `Hypermap.nodeDegree H u fuel < 5`. -/
theorem rsstShift_eq_zero_of_deg_lt_5 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u v : H.Dart)
    (h_lt : Hypermap.nodeDegree H u fuel < 5) :
    rsstShift H fuel u v = 0 := by
  dsimp [rsstShift]
  rw [vertexRuleOutflow_eq_zero_of_target_deg_lt_5 H darts h_all h_le v u h_lt,
      vertexRuleOutflow_eq_zero_of_deg_lt_5 H darts h_all h_le u v h_lt]
  rfl

/-- Vertex outflow `vertexRuleOutflow H fuel u v = 0` when `9 ≤ Hypermap.nodeDegree H u fuel`. -/
theorem vertexRuleOutflow_eq_zero_of_deg_ge_9 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u v : H.Dart)
    (h_ge : 9 ≤ Hypermap.nodeDegree H u fuel) :
    vertexRuleOutflow H fuel u v = 0 := by
  dsimp [vertexRuleOutflow]
  split
  · rfl
  · apply foldl_add_eq_zero
    intro d hd
    have hd_orb : d ∈ getOrbit H.node fuel u := (List.mem_filter.mp hd).1
    have hd_deg : Hypermap.nodeDegree H d fuel = Hypermap.nodeDegree H u fuel :=
      nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hd_orb
    exact dartRuleOutflow_eq_zero_of_deg_ge_9 H fuel d (by omega)

/-- For any vertex `u` with `9 ≤ Hypermap.nodeDegree H u fuel`, `rsstShift H fuel u v = vertexRuleOutflow H fuel v u` (`≥ 0`). -/
theorem rsstShift_eq_inflow_of_deg_ge_9 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u v : H.Dart)
    (h_ge : 9 ≤ Hypermap.nodeDegree H u fuel) :
    rsstShift H fuel u v = vertexRuleOutflow H fuel v u := by
  dsimp [rsstShift]
  rw [vertexRuleOutflow_eq_zero_of_deg_ge_9 H darts h_all h_le u v h_ge]
  omega

/-- No vertex `u` of degree `≠ 5` sends any charge to a vertex `v` of degree `5`. -/
theorem vertexRuleOutflow_eq_zero_of_target_deg_5_of_deg_ne_5 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u v : H.Dart)
    (h_v : Hypermap.nodeDegree H v fuel = 5)
    (h_u : Hypermap.nodeDegree H u fuel ≠ 5) :
    vertexRuleOutflow H fuel u v = 0 := by
  dsimp [vertexRuleOutflow]
  split
  · rfl
  · apply foldl_add_eq_zero
    intro d hd
    have hd_orb : d ∈ getOrbit H.node fuel u := (List.mem_filter.mp hd).1
    have hd_same : Hypermap.sameVertex H (H.edge.f d) v fuel = true := (List.mem_filter.mp hd).2
    have hd_deg : Hypermap.nodeDegree H d fuel = Hypermap.nodeDegree H u fuel :=
      nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hd_orb
    have hed_deg : Hypermap.nodeDegree H (H.edge.f d) fuel = 5 := by
      rw [← h_v]
      exact (nodeDegree_eq_of_sameVertex H darts h_all h_le hd_same).symm
    exact dartRuleOutflow_eq_zero_of_target_deg_5_of_deg_ne_5 H fuel d hed_deg (by omega)

/-!
### Stage C.3: Local `netDartShift` & `orbitNetShift` Discharging Bounds for Degrees $5$ and $\ge 12$
-/

/-- Net charge shift across directed dart `d`: inflow along `H.edge.f d` minus outflow along `d`. -/
def netDartShift (H : Hypermap) [DecidableEq H.Dart] (fuel : Nat) (d : H.Dart) : Int :=
  dartRuleOutflow H fuel (H.edge.f d) - dartRuleOutflow H fuel d

/-- Total net charge shift summed locally over the vertex orbit `getOrbit H.node fuel u`. -/
def orbitNetShift (H : Hypermap) [DecidableEq H.Dart] (fuel : Nat) (u : H.Dart) : Int :=
  (getOrbit H.node fuel u).foldl (fun acc d => acc + netDartShift H fuel d) 0

/-- When both `d` and `H.edge.f d` have degree `5` (and `H.edge.f (H.edge.f d) = d`),
    Rule 1 sends `2` units in each direction and all other rules send `0`, so `netDartShift H fuel d = 0`. -/
theorem netDartShift_eq_zero_of_deg_5_of_target_deg_5 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_inv : H.edge.f (H.edge.f d) = d)
    (h_d : Hypermap.nodeDegree H d fuel = 5)
    (h_ed : Hypermap.nodeDegree H (H.edge.f d) fuel = 5) :
    netDartShift H fuel d = 0 := by
  dsimp [netDartShift]
  have h_out : dartRuleOutflow H fuel d = 2 :=
    dartRuleOutflow_eq_two_of_deg_5_of_target_deg_5 H fuel d h_d h_ed
  have h_in : dartRuleOutflow H fuel (H.edge.f d) = 2 := by
    apply dartRuleOutflow_eq_two_of_deg_5_of_target_deg_5 H fuel (H.edge.f d) h_ed
    rw [h_inv]
    exact h_d
  omega

/-- When `d` has degree `5` and `H.edge.f d` has degree `≥ 6` (with `H.edge.f (H.edge.f d) = d`),
    inflow is `0` and outflow is `≥ 2`, so `netDartShift H fuel d ≤ -2`. -/
theorem netDartShift_le_neg_two_of_deg_5_of_target_deg_ge_6 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_inv : H.edge.f (H.edge.f d) = d)
    (h_d : Hypermap.nodeDegree H d fuel = 5)
    (h_ed : 6 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    netDartShift H fuel d ≤ -2 := by
  dsimp [netDartShift]
  have h_out : 2 ≤ dartRuleOutflow H fuel d :=
    two_le_dartRuleOutflow_of_deg_5_of_target_deg_ge_5 H fuel d h_d (by omega)
  have h_in : dartRuleOutflow H fuel (H.edge.f d) = 0 := by
    apply dartRuleOutflow_eq_zero_of_target_deg_5_of_deg_ne_5 H fuel (H.edge.f d)
    · rw [h_inv]; exact h_d
    · omega
  omega

/-- When `d` has degree `5` and `H.edge.f d` has degree `≥ 5` (with `H.edge.f (H.edge.f d) = d`),
    `netDartShift H fuel d ≤ 0`. -/
theorem netDartShift_le_zero_of_deg_5_of_target_deg_ge_5 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_inv : H.edge.f (H.edge.f d) = d)
    (h_d : Hypermap.nodeDegree H d fuel = 5)
    (h_ed : 5 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    netDartShift H fuel d ≤ 0 := by
  by_cases h5 : Hypermap.nodeDegree H (H.edge.f d) fuel = 5
  · rw [netDartShift_eq_zero_of_deg_5_of_target_deg_5 H fuel d h_inv h_d h5]
    omega
  · have h6 : 6 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel := by omega
    have h_le := netDartShift_le_neg_two_of_deg_5_of_target_deg_ge_6 H fuel d h_inv h_d h6
    omega

/-- When `9 ≤ Hypermap.nodeDegree H d fuel`, outflow is `0`, so `netDartShift H fuel d = dartRuleOutflow H fuel (H.edge.f d)`. -/
theorem netDartShift_eq_inflow_of_deg_ge_9 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart) (h_ge : 9 ≤ Hypermap.nodeDegree H d fuel) :
    netDartShift H fuel d = dartRuleOutflow H fuel (H.edge.f d) := by
  dsimp [netDartShift]
  rw [dartRuleOutflow_eq_zero_of_deg_ge_9 H fuel d h_ge]
  omega

/-- Local Discharging Bound for Degree 5:
    if `Hypermap.nodeDegree H u fuel = 5` on a complete dart list (`darts.length ≤ fuel`)
    and every neighbor dart `H.edge.f d` (`d ∈ getOrbit H.node fuel u`) has degree `≥ 6`,
    then `orbitNetShift H fuel u ≤ -10` and `initialCharge H u fuel + orbitNetShift H fuel u ≤ 0`. -/
theorem initialCharge_add_orbitNetShift_le_zero_of_deg_5 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_inv : ∀ d ∈ getOrbit H.node fuel u, H.edge.f (H.edge.f d) = d)
    (h_deg5 : Hypermap.nodeDegree H u fuel = 5)
    (h_nb6 : ∀ d ∈ getOrbit H.node fuel u, 6 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    initialCharge H u fuel + orbitNetShift H fuel u ≤ 0 := by
  dsimp [initialCharge, orbitNetShift]
  have h_bound :
      (getOrbit H.node fuel u).foldl (fun acc d => acc + netDartShift H fuel d) 0 ≤
        (-2 : Int) * ((getOrbit H.node fuel u).length : Int) := by
    apply foldl_add_le_of_le_const
    intro d hd
    have hd_deg : Hypermap.nodeDegree H d fuel = 5 := by
      rw [nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hd, h_deg5]
    exact netDartShift_le_neg_two_of_deg_5_of_target_deg_ge_6 H fuel d (h_inv d hd) hd_deg (h_nb6 d hd)
  change (getOrbit H.node fuel u).length = 5 at h_deg5
  change 10 * (6 - ((getOrbit H.node fuel u).length : Int)) +
    (getOrbit H.node fuel u).foldl (fun acc d => acc + netDartShift H fuel d) 0 ≤ 0
  omega


/-- Local Discharging Bound for Degree `≥ 12`:
    if `12 ≤ Hypermap.nodeDegree H u fuel` on a complete dart list (`darts.length ≤ fuel`)
    and every incoming dart `H.edge.f d` (`d ∈ getOrbit H.node fuel u`) has `dartRuleOutflow ≤ 5`,
    then `initialCharge H u fuel + orbitNetShift H fuel u ≤ 0`. -/
theorem initialCharge_add_orbitNetShift_le_zero_of_deg_ge_12 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_deg12 : 12 ≤ Hypermap.nodeDegree H u fuel)
    (h_in5 : ∀ d ∈ getOrbit H.node fuel u, dartRuleOutflow H fuel (H.edge.f d) ≤ 5) :
    initialCharge H u fuel + orbitNetShift H fuel u ≤ 0 := by
  dsimp [initialCharge, orbitNetShift]
  have h_bound :
      (getOrbit H.node fuel u).foldl (fun acc d => acc + netDartShift H fuel d) 0 ≤
        (5 : Int) * ((getOrbit H.node fuel u).length : Int) := by
    apply foldl_add_le_of_le_const
    intro d hd
    have hd_deg : 9 ≤ Hypermap.nodeDegree H d fuel := by
      have := nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hd
      omega
    rw [netDartShift_eq_inflow_of_deg_ge_9 H fuel d hd_deg]
    exact h_in5 d hd
  change 12 ≤ (getOrbit H.node fuel u).length at h_deg12
  change 10 * (6 - ((getOrbit H.node fuel u).length : Int)) +
    (getOrbit H.node fuel u).foldl (fun acc d => acc + netDartShift H fuel d) 0 ≤ 0
  omega

/-- Fuel-independence of `sumShiftsTo (rsstChargeShift H fuel)` on any complete dart list. -/
theorem sumShiftsTo_rsstChargeShift_fuel_eq_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    (u : H.Dart) (vs : List H.Dart) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    sumShiftsTo (rsstChargeShift H fuel) u vs =
      sumShiftsTo (rsstChargeShift H darts.length) u vs := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    dsimp [sumShiftsTo]
    change rsstShift H fuel u v + sumShiftsTo (rsstChargeShift H fuel) u vs =
      rsstShift H darts.length u v + sumShiftsTo (rsstChargeShift H darts.length) u vs
    rw [rsstShift_fuel_eq_of_complete H darts h_all u v h_le, ih]

/-- Fuel-independence of `finalCharge H (rsstChargeShift H fuel)` on any complete dart list. -/
theorem finalCharge_rsstChargeShift_fuel_eq_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    (u : H.Dart) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    finalCharge H (rsstChargeShift H fuel) darts u =
      finalCharge H (rsstChargeShift H darts.length) darts u := by
  dsimp [finalCharge]
  rw [sumShiftsTo_rsstChargeShift_fuel_eq_of_complete H darts h_all u _ h_le]

/-- When `Hypermap.nodeDegree H u fuel < 5`, `sumShiftsTo (rsstChargeShift H fuel) u vs = 0` for any vertex list `vs`. -/
theorem sumShiftsTo_eq_zero_of_deg_lt_5 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_lt : Hypermap.nodeDegree H u fuel < 5) (vs : List H.Dart) :
    sumShiftsTo (rsstChargeShift H fuel) u vs = 0 := by
  induction vs with
  | nil => rfl
  | cons v vs ih =>
    dsimp [sumShiftsTo]
    change rsstShift H fuel u v + sumShiftsTo (rsstChargeShift H fuel) u vs = 0
    rw [rsstShift_eq_zero_of_deg_lt_5 H darts h_all h_le u v h_lt, ih]
    rfl

/-- When `Hypermap.nodeDegree H u darts.length < 5`, `finalCharge` equals `initialCharge` (`> 0`). -/
theorem finalCharge_eq_initialCharge_of_deg_lt_5 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_lt : Hypermap.nodeDegree H u darts.length < 5) :
    finalCharge H (rsstChargeShift H fuel) darts u = initialCharge H u darts.length := by
  rw [finalCharge_rsstChargeShift_fuel_eq_of_complete H darts h_all u h_le]
  dsimp [finalCharge]
  rw [sumShiftsTo_eq_zero_of_deg_lt_5 H darts h_all (Nat.le_refl _) u h_lt]
  omega

/-- When `9 ≤ Hypermap.nodeDegree H u fuel`, `sumShiftsTo (rsstChargeShift H fuel) u vs ≥ 0` for any vertex list `vs`. -/
theorem sumShiftsTo_nonneg_of_deg_ge_9 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_ge : 9 ≤ Hypermap.nodeDegree H u fuel) (vs : List H.Dart) :
    0 ≤ sumShiftsTo (rsstChargeShift H fuel) u vs := by
  induction vs with
  | nil =>
    dsimp [sumShiftsTo]
    omega
  | cons v vs ih =>
    dsimp [sumShiftsTo]
    change 0 ≤ rsstShift H fuel u v + sumShiftsTo (rsstChargeShift H fuel) u vs
    rw [rsstShift_eq_inflow_of_deg_ge_9 H darts h_all h_le u v h_ge]
    have hv : 0 ≤ vertexRuleOutflow H fuel v u := vertexRuleOutflow_nonneg H fuel v u
    omega


/-- When `Hypermap.nodeDegree H u fuel = 5` and `5 ≤ Hypermap.nodeDegree H v fuel` with `¬ sameVertex H u v fuel`,
    `vertexRuleOutflow H fuel u v` is at least `2` times the number of darts from `u` to `v`. -/
theorem two_mul_length_le_vertexRuleOutflow_of_deg_5 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u v : H.Dart)
    (h_not_same : Hypermap.sameVertex H u v fuel = false)
    (h_u : Hypermap.nodeDegree H u fuel = 5)
    (h_v : 5 ≤ Hypermap.nodeDegree H v fuel) :
    2 * (((getOrbit H.node fuel u).filter (fun d => Hypermap.sameVertex H (H.edge.f d) v fuel)).length : Int) ≤
      vertexRuleOutflow H fuel u v := by
  dsimp [vertexRuleOutflow]
  rw [h_not_same]
  dsimp
  apply foldl_add_ge_of_ge_const
  intro d hd
  have hd_orb : d ∈ getOrbit H.node fuel u := (List.mem_filter.mp hd).1
  have hd_same : Hypermap.sameVertex H (H.edge.f d) v fuel = true := (List.mem_filter.mp hd).2
  have hd_deg : Hypermap.nodeDegree H d fuel = 5 := by
    rw [nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hd_orb, h_u]
  have hed_deg : 5 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel := by
    have := nodeDegree_eq_of_sameVertex H darts h_all h_le hd_same
    omega
  exact two_le_dartRuleOutflow_of_deg_5_of_target_deg_ge_5 H fuel d hd_deg hed_deg

/-!
### Stage D.1: Primal–Dual Hypermap Bridge (`H` ↔ `H.dual`)
-/

instance instDecidableEqDualDart (H : Hypermap) [DecidableEq H.Dart] : DecidableEq H.dual.Dart :=
  inferInstanceAs (DecidableEq H.Dart)

/-- Fuel-independence of `sameFace` on any complete dart list. -/
theorem sameFace_fuel_eq_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    (d1 d2 : H.Dart) {fuel : Nat} (h_le : darts.length ≤ fuel) :
    Hypermap.sameFace H d1 d2 fuel = Hypermap.sameFace H d1 d2 darts.length := by
  dsimp [Hypermap.sameFace]
  rw [Hypermap.getOrbit_fuel_eq_of_complete H.face darts h_all d1 h_le]

/-- On a complete dart list (`darts.length ≤ fuel`), `sameVertex` on `H.dual` equals `sameFace` on `H`. -/
theorem sameVertex_dual_eq_sameFace_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u v : H.Dart) :
    Hypermap.sameVertex H.dual u v fuel = Hypermap.sameFace H u v fuel := by
  dsimp [Hypermap.sameVertex, Hypermap.sameFace, _root_.Hypermap.dual]
  exact _root_.Hypermap.getOrbit_symm_contains_eq_of_complete H.face darts h_all h_le u v

/-- On a complete dart list (`darts.length ≤ fuel`), `sameFace` on `H.dual` equals `sameVertex` on `H`. -/
theorem sameFace_dual_eq_sameVertex_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u v : H.Dart) :
    Hypermap.sameFace H.dual u v fuel = Hypermap.sameVertex H u v fuel := by
  dsimp [Hypermap.sameFace, Hypermap.sameVertex, _root_.Hypermap.dual]
  exact _root_.Hypermap.getOrbit_symm_contains_eq_of_complete H.node darts h_all h_le u v

/-- A dart `d` is a self-loop in `H.dual` (`sameVertex H.dual d (H.dual.edge.f d) fuel`)
    if and only if `d` is a bridge in `H` (`isBridge H d fuel`). -/
theorem sameVertex_dual_edge_eq_isBridge_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (d : H.Dart) :
    Hypermap.sameVertex H.dual d (H.dual.edge.f d) fuel = Hypermap.isBridge H d fuel := by
  dsimp [Hypermap.isBridge]
  exact sameVertex_dual_eq_sameFace_of_complete H darts h_all h_le d (H.edge.f d)

/-- If every dart in `H` is not a self-loop (`sameVertex H d (H.edge.f d) fuel = false`),
    then for every vertex `u` and every `d ∈ getOrbit H.node fuel u`, `sameVertex H (H.edge.f d) u fuel = false`. -/
theorem loopless_orbit_of_forall_sameVertex_edge_false (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_noloop : ∀ d : H.Dart, Hypermap.sameVertex H d (H.edge.f d) fuel = false)
    (u : H.Dart) :
    ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false := by
  intro d hd
  have hud : Hypermap.sameVertex H u d fuel = true := List.contains_iff_mem.mpr hd
  cases h_eu : Hypermap.sameVertex H (H.edge.f d) u fuel with
  | false => rfl
  | true =>
    have h_ed : Hypermap.sameVertex H (H.edge.f d) d fuel = true :=
      sameVertex_trans_of_complete H darts h_all h_le h_eu hud
    have h_de : Hypermap.sameVertex H d (H.edge.f d) fuel = true := by
      rw [sameVertex_symm_of_complete H darts h_all h_le d (H.edge.f d)]
      exact h_ed
    rw [h_noloop d] at h_de
    contradiction

/-- When `H` is bridgeless (`isBridgeless H darts fuel_b` with `darts.length ≤ fuel_b`),
    `H.dual` has no self-loops at any dart (`sameVertex H.dual d (H.dual.edge.f d) fuel = false`). -/
theorem dual_sameVertex_edge_eq_false_of_isBridgeless (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b fuel : Nat} (h_le_b : darts.length ≤ fuel_b) (h_le : darts.length ≤ fuel)
    (h_bridge : Hypermap.isBridgeless H darts fuel_b) (d : H.Dart) :
    Hypermap.sameVertex H.dual d (H.dual.edge.f d) fuel = false := by
  rw [sameVertex_dual_edge_eq_isBridge_of_complete H darts h_all h_le d]
  have h_b_eq : Hypermap.isBridge H d fuel = Hypermap.isBridge H d fuel_b := by
    dsimp [Hypermap.isBridge]
    rw [sameFace_fuel_eq_of_complete H darts h_all d (H.edge.f d) h_le,
        sameFace_fuel_eq_of_complete H darts h_all d (H.edge.f d) h_le_b]
  rw [h_b_eq]
  exact h_bridge d (h_all d)

/-- When `H` is bridgeless, every vertex orbit of `H.dual` is loopless. -/
theorem dual_loopless_orbit_of_isBridgeless (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b fuel : Nat} (h_le_b : darts.length ≤ fuel_b) (h_le : darts.length ≤ fuel)
    (h_bridge : Hypermap.isBridgeless H darts fuel_b) (u : H.Dart) :
    ∀ d ∈ getOrbit H.dual.node fuel u,
      Hypermap.sameVertex H.dual (H.dual.edge.f d) u fuel = false :=
  loopless_orbit_of_forall_sameVertex_edge_false H.dual darts h_all h_le
    (dual_sameVertex_edge_eq_false_of_isBridgeless H darts h_all h_le_b h_le h_bridge) u

/-- On a complete dart list (`darts.length ≤ fuel`), `nodeDegree` on `H.dual` equals `faceDegree` on `H`. -/
theorem nodeDegree_dual_eq_faceDegree_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (d : H.Dart) :
    Hypermap.nodeDegree H.dual d fuel = Hypermap.faceDegree H d fuel := by
  dsimp [Hypermap.nodeDegree, Hypermap.faceDegree, _root_.Hypermap.dual]
  exact _root_.Hypermap.getOrbit_symm_length_eq_of_complete H.face darts h_all h_le d

/-- On a complete dart list (`darts.length ≤ fuel`), `faceDegree` on `H.dual` equals `nodeDegree` on `H`. -/
theorem faceDegree_dual_eq_nodeDegree_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (d : H.Dart) :
    Hypermap.faceDegree H.dual d fuel = Hypermap.nodeDegree H d fuel := by
  dsimp [Hypermap.faceDegree, Hypermap.nodeDegree, _root_.Hypermap.dual]
  exact _root_.Hypermap.getOrbit_symm_length_eq_of_complete H.node darts h_all h_le d

/-- `H.dual` is a triangulation (`faceDegree = 3`) if and only if `H` is cubic (`nodeDegree = 3`). -/
theorem dual_triangulation_iff_cubic (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) :
    (∀ d ∈ darts, Hypermap.faceDegree H.dual d fuel = 3) ↔
      (∀ d ∈ darts, Hypermap.nodeDegree H d fuel = 3) := by
  constructor <;> intro h d hd
  · rw [← faceDegree_dual_eq_nodeDegree_of_complete H darts h_all h_le d]
    exact h d hd
  · rw [faceDegree_dual_eq_nodeDegree_of_complete H darts h_all h_le d]
    exact h d hd

/-- Equivalence between 4-face-colorability of `H` and 4-vertex-colorability of `H.dual`. -/
theorem nonempty_faceColoring_iff_nonempty_vertexColoring_dual (H : Hypermap) :
    Nonempty (_root_.Hypermap.FaceColoring H) ↔ Nonempty (_root_.Hypermap.VertexColoring H.dual) :=
  ⟨fun ⟨fc⟩ => ⟨_root_.Hypermap.faceColoringToVertexColoringOfDual H fc⟩,
   fun ⟨vc⟩ => ⟨_root_.Hypermap.vertexColoringOfDualToFaceColoring H vc⟩⟩

/-- On a complete dart list (`darts.length ≤ fuel`), `numNodes H.dual = numFaces H`. -/
theorem numNodes_dual_eq_numFaces_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (l : List H.Dart) :
    _root_.Hypermap.numNodes H.dual fuel l = _root_.Hypermap.numFaces H fuel l := by
  dsimp [_root_.Hypermap.numNodes, _root_.Hypermap.numFaces, _root_.Hypermap.dual]
  exact _root_.Hypermap.countOrbits_symm_perm_of_complete H.face darts h_all h_le l

/-- On a complete dart list (`darts.length ≤ fuel`), `numFaces H.dual = numNodes H`. -/
theorem numFaces_dual_eq_numNodes_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (l : List H.Dart) :
    _root_.Hypermap.numFaces H.dual fuel l = _root_.Hypermap.numNodes H fuel l := by
  dsimp [_root_.Hypermap.numFaces, _root_.Hypermap.numNodes, _root_.Hypermap.dual]
  exact _root_.Hypermap.countOrbits_symm_perm_of_complete H.node darts h_all h_le l

/-- `numEdges H.dual` is definitionally equal to `numEdges H`. -/
theorem numEdges_dual_eq_numEdges (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (l : List H.Dart) :
    _root_.Hypermap.numEdges H.dual fuel l = _root_.Hypermap.numEdges H fuel l :=
  rfl

/-- On a complete dart list (`darts.length ≤ fuel`), `EulerChar H.dual = EulerChar H`. -/
theorem EulerChar_dual_eq_EulerChar_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (l : List H.Dart) :
    _root_.Hypermap.EulerChar H.dual fuel l = _root_.Hypermap.EulerChar H fuel l := by
  dsimp [_root_.Hypermap.EulerChar]
  rw [numNodes_dual_eq_numFaces_of_complete H darts h_all h_le l,
      numFaces_dual_eq_numNodes_of_complete H darts h_all h_le l]
  omega

/-- Primal-to-Dual Triangulation Euler & Handshaking Package:
    for any complete, bridgeless, connected, cubic planar hypermap `H`,
    its dual triangulation `H.dual` satisfies the three Euler/handshaking equations:
    1. `sumDegrees = 2 * E`
    2. `V_dual - E + F_dual = 2`
    3. `2 * E = 3 * F_dual` -/
theorem dual_triangulation_euler_equations_of_cubic (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b : Nat} (h_bridge : Hypermap.isBridgeless H darts fuel_b)
    {fuel_deg fuel : Nat} (h_deg_le : darts.length ≤ fuel_deg) (h_le : darts.length ≤ fuel)
    (h_planar : _root_.Hypermap.isPlanar H fuel darts = true)
    (h_conn : _root_.Hypermap.numComponents H fuel darts = 1)
    (h_cubic : ∀ d ∈ darts, Hypermap.nodeDegree H d fuel = 3) :
    ∃ (E F_dual : Int),
      sumDegrees (fun v => (Hypermap.nodeDegree H.dual v fuel_deg : Int))
        (Hypermap.extractGraph H.dual darts).vertices = 2 * E ∧
      ((Hypermap.extractGraph H.dual darts).vertices.length : Int) - E + F_dual = 2 ∧
      2 * E = 3 * F_dual := by
  refine ⟨(_root_.Hypermap.numEdges H fuel darts : Int), (_root_.Hypermap.numNodes H fuel darts : Int), ?_, ?_, ?_⟩
  · rw [sumDegrees_extractGraph_eq_length H.dual darts h_nodup h_all h_deg_le]
    have hE := _root_.Hypermap.darts_length_eq_two_mul_numEdges H darts h_nodup h_all h_bridge h_le
    omega
  · have h_euler := _root_.Hypermap.euler_char_eq_of_isPlanar H fuel darts h_planar
    dsimp [_root_.Hypermap.EulerChar] at h_euler
    rw [_root_.Hypermap.extractGraph_vertices_length_eq_numNodes H.dual darts darts.length]
    have h_nodes_dual : _root_.Hypermap.numNodes H.dual fuel darts =
        _root_.Hypermap.numNodes H.dual darts.length darts :=
      _root_.Hypermap.countOrbits_fuel_eq_of_complete H.dual.node darts darts h_all h_le
    rw [← h_nodes_dual, numNodes_dual_eq_numFaces_of_complete H darts h_all h_le darts]
    omega
  · have h_tri : ∀ d ∈ darts, (getOrbit H.dual.face fuel d).length = 3 := by
      intro d hd
      change Hypermap.faceDegree H.dual d fuel = 3
      rw [faceDegree_dual_eq_nodeDegree_of_complete H darts h_all h_le d]
      exact h_cubic d hd
    have hF := _root_.Hypermap.darts_length_eq_three_mul_numFaces_of_triangulation H.dual
      darts h_nodup h_all h_le h_tri
    rw [numFaces_dual_eq_numNodes_of_complete H darts h_all h_le darts] at hF
    have hE := _root_.Hypermap.darts_length_eq_two_mul_numEdges H darts h_nodup h_all h_bridge h_le
    omega

/-- Unconditional Initial Charge Sum = 120 on `H.dual` for any complete, bridgeless, connected, cubic planar hypermap `H`. -/
theorem dual_initial_charge_sum_eq_120_of_cubic (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b : Nat} (h_bridge : Hypermap.isBridgeless H darts fuel_b)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_planar : _root_.Hypermap.isPlanar H fuel darts = true)
    (h_conn : _root_.Hypermap.numComponents H fuel darts = 1)
    (h_cubic : ∀ d ∈ darts, Hypermap.nodeDegree H d fuel = 3) :
    sumCharges (fun v => initialCharge H.dual v darts.length)
      (Hypermap.extractGraph H.dual darts).vertices = 120 := by
  rcases dual_triangulation_euler_equations_of_cubic H darts h_nodup h_all h_bridge
      (Nat.le_refl _) h_le h_planar h_conn h_cubic with ⟨E, F_dual, h1, h2, h3⟩
  exact initial_charge_sum_eq_120_of_triangulation H.dual
    (Hypermap.extractGraph H.dual darts).vertices darts.length E F_dual h1 h2 h3

/-!
### Stage D.2: Global-to-Local Outflow, Inflow & `rsstShift` Decomposition
-/

theorem foldl_add_congr {α : Type} (l : List α) (f g : α → Int)
    (h : ∀ x ∈ l, f x = g x) (init : Int) :
    l.foldl (fun acc x => acc + f x) init = l.foldl (fun acc x => acc + g x) init := by
  induction l generalizing init with
  | nil => rfl
  | cons a as ih =>
    dsimp [List.foldl]
    rw [h a (List.Mem.head as)]
    exact ih (fun x hx => h x (List.Mem.tail a hx)) (init + g a)

theorem foldl_add_add {α : Type} (l : List α) (f g : α → Int) :
    l.foldl (fun acc x => acc + (f x + g x)) 0 =
      l.foldl (fun acc x => acc + f x) 0 + l.foldl (fun acc x => acc + g x) 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [foldl_add_cons, foldl_add_cons, foldl_add_cons, ih]
    omega

theorem foldl_add_sub {α : Type} (l : List α) (f g : α → Int) :
    l.foldl (fun acc x => acc + (f x - g x)) 0 =
      l.foldl (fun acc x => acc + f x) 0 - l.foldl (fun acc x => acc + g x) 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [foldl_add_cons, foldl_add_cons, foldl_add_cons, ih]
    omega

theorem foldl_add_filter {α : Type} (l : List α) (P : α → Bool) (f : α → Int) :
    (l.filter P).foldl (fun acc x => acc + f x) 0 =
      l.foldl (fun acc x => acc + if P x then f x else 0) 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    rw [foldl_add_cons]
    dsimp [List.filter]
    cases hP : P a
    · dsimp
      rw [ih]
      omega
    · dsimp
      rw [foldl_add_shift _ f (0 + f a), ih]
      omega

theorem foldl_add_map {α β : Type} (l : List α) (g : α → β) (f : β → Int) :
    (l.map g).foldl (fun acc y => acc + f y) 0 =
      l.foldl (fun acc x => acc + f (g x)) 0 := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    change (g a :: as.map g).foldl (fun acc y => acc + f y) 0 =
      (a :: as).foldl (fun acc x => acc + f (g x)) 0
    rw [foldl_add_cons, foldl_add_cons, ih]

theorem filter_eq_self_of_forall_true {α : Type} (P : α → Bool) (l : List α)
    (h : ∀ x ∈ l, P x = true) : l.filter P = l := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    dsimp [List.filter]
    rw [h a (List.Mem.head as)]
    dsimp
    congr 1
    exact ih (fun x hx => h x (List.Mem.tail a hx))

/-- Splitting `f a` out of an additive `foldl` over a duplicate-free list `l` when `a ∈ l`. -/
theorem foldl_add_eq_add_filter_ne {α : Type} [DecidableEq α] (l : List α) (f : α → Int)
    (hl : l.Nodup) {a : α} (ha : a ∈ l) :
    l.foldl (fun acc x => acc + f x) 0 =
      f a + (l.filter (fun x => !(x == a))).foldl (fun acc x => acc + f x) 0 := by
  induction l with
  | nil => cases ha
  | cons b bs ih =>
    have hb_not : b ∉ bs := (List.nodup_cons.mp hl).1
    have hbs_nodup : bs.Nodup := (List.nodup_cons.mp hl).2
    rw [foldl_add_cons]
    rcases List.mem_cons.mp ha with rfl | ha_bs
    · dsimp [List.filter]
      have haa : (!(a == a)) = false := by simp
      rw [haa]
      dsimp
      have h_flt_eq : bs.filter (fun x => !(x == a)) = bs := by
        apply filter_eq_self_of_forall_true
        intro x hx
        have h_ne : x ≠ a := fun h_eq => hb_not (h_eq ▸ hx)
        simp [h_ne]
      rw [h_flt_eq]
    · have hba_ne : b ≠ a := fun h_eq => hb_not (h_eq ▸ ha_bs)
      have hba : (!(b == a)) = true := by simp [hba_ne]
      dsimp [List.filter]
      rw [hba]
      dsimp
      rw [foldl_add_shift _ f (0 + f b), ih hbs_nodup ha_bs]
      omega

/-- Any two duplicate-free (`Nodup`) lists with identical membership have identical additive `foldl` sums. -/
theorem nodup_foldl_add_eq_of_iff_mem {α : Type} [DecidableEq α] {l1 l2 : List α} (f : α → Int)
    (hl1 : l1.Nodup) (hl2 : l2.Nodup) (h_iff : ∀ x, x ∈ l1 ↔ x ∈ l2) :
    l1.foldl (fun acc x => acc + f x) 0 = l2.foldl (fun acc x => acc + f x) 0 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => rfl
    | cons b bs =>
      have hb : b ∈ ([] : List α) := (h_iff b).mpr (List.Mem.head bs)
      cases hb
  | cons a as ih =>
    have ha_not : a ∉ as := (List.nodup_cons.mp hl1).1
    have has_nodup : as.Nodup := (List.nodup_cons.mp hl1).2
    have ha_l2 : a ∈ l2 := (h_iff a).mp (List.Mem.head as)
    rw [foldl_add_cons, foldl_add_eq_add_filter_ne l2 f hl2 ha_l2]
    have h_flt_nodup : (l2.filter (fun x => !(x == a))).Nodup :=
      _root_.Hypermap.nodup_filter (fun x => !(x == a)) hl2
    have h_iff_rest : ∀ x, x ∈ as ↔ x ∈ l2.filter (fun x => !(x == a)) := by
      intro x
      rw [List.mem_filter]
      constructor
      · intro hx_as
        have hx_ne : x ≠ a := fun h_eq => ha_not (h_eq ▸ hx_as)
        refine ⟨(h_iff x).mp (List.Mem.tail a hx_as), ?_⟩
        simp [hx_ne]
      · rintro ⟨hx_l2, hx_ne_b⟩
        have hx_ne : x ≠ a := by
          intro h_eq
          subst h_eq
          simp at hx_ne_b
        rcases List.mem_cons.mp ((h_iff x).mpr hx_l2) with rfl | hx_as
        · exact False.elim (hx_ne rfl)
        · exact hx_as
    rw [ih has_nodup h_flt_nodup h_iff_rest]

theorem nodup_map_of_injective {α : Type} (g : α → α) (h_inj : ∀ x y, g x = g y → x = y)
    {l : List α} (hl : l.Nodup) : (l.map g).Nodup := by
  induction l with
  | nil => exact List.Pairwise.nil
  | cons a as ih =>
    have ha_not : a ∉ as := (List.nodup_cons.mp hl).1
    have has_nodup : as.Nodup := (List.nodup_cons.mp hl).2
    dsimp [List.map]
    refine List.nodup_cons.mpr ⟨?_, ih has_nodup⟩
    intro h_mem
    rcases List.mem_map.mp h_mem with ⟨x, hx_as, h_gx⟩
    have h_eq : x = a := h_inj x a h_gx
    subst h_eq
    exact ha_not hx_as

/-- Key Inflow-to-Local-Orbit Re-indexing Theorem:
    the total inflow `vertexRuleOutflow H fuel v u` from `v` to `u` equals the sum of
    `dartRuleOutflow H fuel (H.edge.f d)` over all darts `d ∈ getOrbit H.node fuel u`
    whose opposite dart `H.edge.f d` belongs to `v`. -/
theorem vertexRuleOutflow_opp_eq_filter_u (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u v : H.Dart) :
    vertexRuleOutflow H fuel v u =
      if Hypermap.sameVertex H u v fuel then 0
      else ((getOrbit H.node fuel u).filter (fun d => Hypermap.sameVertex H (H.edge.f d) v fuel)).foldl
        (fun acc d => acc + dartRuleOutflow H fuel (H.edge.f d)) 0 := by
  dsimp [vertexRuleOutflow]
  rw [sameVertex_symm_of_complete H darts h_all h_le v u]
  cases h_uv : Hypermap.sameVertex H u v fuel with
  | true => rfl
  | false =>
    dsimp
    let L_u := (getOrbit H.node fuel u).filter (fun d => Hypermap.sameVertex H (H.edge.f d) v fuel)
    let L_v := (getOrbit H.node fuel v).filter (fun e => Hypermap.sameVertex H (H.edge.f e) u fuel)
    have h_Lu_nodup : L_u.Nodup :=
      _root_.Hypermap.nodup_filter _ (_root_.Hypermap.getOrbit_nodup H.node fuel u)
    have h_Lv_nodup : L_v.Nodup :=
      _root_.Hypermap.nodup_filter _ (_root_.Hypermap.getOrbit_nodup H.node fuel v)
    have h_inj : ∀ x y : H.Dart, H.edge.f x = H.edge.f y → x = y := by
      intro x y h_eq
      have h2 := congrArg H.edge.f h_eq
      rw [H.edge_involution x, H.edge_involution y] at h2
      exact h2
    have h_map_nodup : (L_u.map H.edge.f).Nodup := nodup_map_of_injective H.edge.f h_inj h_Lu_nodup
    have h_iff : ∀ e : H.Dart, e ∈ L_v ↔ e ∈ L_u.map H.edge.f := by
      intro e
      rw [List.mem_filter, List.mem_map]
      constructor
      · rintro ⟨he_v, he_u⟩
        refine ⟨H.edge.f e, ?_, H.edge_involution e⟩
        rw [List.mem_filter]
        have h_ue : Hypermap.sameVertex H u (H.edge.f e) fuel = true := by
          rw [sameVertex_symm_of_complete H darts h_all h_le u (H.edge.f e)]
          exact he_u
        have h_ve : Hypermap.sameVertex H v e fuel = true := List.contains_iff_mem.mpr he_v
        have h_ev : Hypermap.sameVertex H (H.edge.f (H.edge.f e)) v fuel = true := by
          rw [H.edge_involution e, sameVertex_symm_of_complete H darts h_all h_le e v]
          exact h_ve
        exact ⟨List.contains_iff_mem.mp h_ue, h_ev⟩
      · rintro ⟨d, hd_Lu, rfl⟩
        have hd_u : d ∈ getOrbit H.node fuel u := (List.mem_filter.mp hd_Lu).1
        have hd_v : Hypermap.sameVertex H (H.edge.f d) v fuel = true := (List.mem_filter.mp hd_Lu).2
        have h_vd : Hypermap.sameVertex H v (H.edge.f d) fuel = true := by
          rw [sameVertex_symm_of_complete H darts h_all h_le v (H.edge.f d)]
          exact hd_v
        have h_ud : Hypermap.sameVertex H u d fuel = true := List.contains_iff_mem.mpr hd_u
        have h_du : Hypermap.sameVertex H (H.edge.f (H.edge.f d)) u fuel = true := by
          rw [H.edge_involution d, sameVertex_symm_of_complete H darts h_all h_le d u]
          exact h_ud
        exact ⟨List.contains_iff_mem.mp h_vd, h_du⟩
    rw [nodup_foldl_add_eq_of_iff_mem (fun e => dartRuleOutflow H fuel e) h_Lv_nodup h_map_nodup h_iff]
    exact foldl_add_map L_u H.edge.f (fun e => dartRuleOutflow H fuel e)

/-- Unified Pairwise Net Charge Shift Formula:
    `rsstShift H fuel u v` equals the sum of `netDartShift H fuel d` over all darts `d` in `u`'s orbit
    whose opposite dart `H.edge.f d` belongs to `v` (and `0` if `sameVertex H u v fuel`). -/
theorem rsstShift_eq_filter_netDartShift (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u v : H.Dart) :
    rsstShift H fuel u v =
      if Hypermap.sameVertex H u v fuel then 0
      else ((getOrbit H.node fuel u).filter (fun d => Hypermap.sameVertex H (H.edge.f d) v fuel)).foldl
        (fun acc d => acc + netDartShift H fuel d) 0 := by
  dsimp [rsstShift]
  rw [vertexRuleOutflow_opp_eq_filter_u H darts h_all h_le u v]
  dsimp [vertexRuleOutflow]
  cases h_uv : Hypermap.sameVertex H u v fuel with
  | true => rfl
  | false =>
    dsimp
    rw [← foldl_add_sub]
    rfl

/-- Between any two degree-5 vertices `u` and `v`, the net charge shift `rsstShift H fuel u v` is `0`. -/
theorem rsstShift_eq_zero_of_deg_5_of_target_deg_5 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u v : H.Dart)
    (h_u : Hypermap.nodeDegree H u fuel = 5)
    (h_v : Hypermap.nodeDegree H v fuel = 5) :
    rsstShift H fuel u v = 0 := by
  rw [rsstShift_eq_filter_netDartShift H darts h_all h_le u v]
  cases h_uv : Hypermap.sameVertex H u v fuel with
  | true => rfl
  | false =>
    dsimp
    apply foldl_add_eq_zero
    intro d hd
    have hd_orb : d ∈ getOrbit H.node fuel u := (List.mem_filter.mp hd).1
    have hd_same : Hypermap.sameVertex H (H.edge.f d) v fuel = true := (List.mem_filter.mp hd).2
    have hd_deg : Hypermap.nodeDegree H d fuel = 5 := by
      rw [nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hd_orb, h_u]
    have hed_deg : Hypermap.nodeDegree H (H.edge.f d) fuel = 5 := by
      have h_eq := nodeDegree_eq_of_sameVertex H darts h_all h_le hd_same
      omega
    exact netDartShift_eq_zero_of_deg_5_of_target_deg_5 H fuel d (H.edge_involution d) hd_deg hed_deg

/-- From a degree-5 vertex `u` to any vertex `v` of degree `≥ 5`, `rsstShift H fuel u v ≤ 0`. -/
theorem rsstShift_le_zero_of_deg_5_of_target_deg_ge_5 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u v : H.Dart)
    (h_u : Hypermap.nodeDegree H u fuel = 5)
    (h_v : 5 ≤ Hypermap.nodeDegree H v fuel) :
    rsstShift H fuel u v ≤ 0 := by
  rw [rsstShift_eq_filter_netDartShift H darts h_all h_le u v]
  cases h_uv : Hypermap.sameVertex H u v fuel with
  | true =>
    dsimp
    omega
  | false =>
    dsimp
    have h_le_c := foldl_add_le_of_le_const
      ((getOrbit H.node fuel u).filter (fun d => Hypermap.sameVertex H (H.edge.f d) v fuel))
      (fun d => netDartShift H fuel d) 0 (by
        intro d hd
        have hd_orb : d ∈ getOrbit H.node fuel u := (List.mem_filter.mp hd).1
        have hd_same : Hypermap.sameVertex H (H.edge.f d) v fuel = true := (List.mem_filter.mp hd).2
        have hd_deg : Hypermap.nodeDegree H d fuel = 5 := by
          rw [nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hd_orb, h_u]
        have hed_deg : 5 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel := by
          have := nodeDegree_eq_of_sameVertex H darts h_all h_le hd_same
          omega
        exact netDartShift_le_zero_of_deg_5_of_target_deg_ge_5 H fuel d (H.edge_involution d) hd_deg hed_deg)
    dsimp at h_le_c
    omega

/-!
### Stage D.3: Global `finalCharge = initialCharge + orbitNetShift` Identity & Degree-5 / Degree-≥12 Bounds
-/

/-- When vertex `u` has no self-loops (`∀ d ∈ getOrbit H.node fuel u, sameVertex H (H.edge.f d) u fuel = false`),
    `rsstShift H fuel u v` simplifies unconditionally (without the `if sameVertex H u v` branch)
    to the `foldl` over `getOrbit H.node fuel u` of `if sameVertex H (H.edge.f d) v fuel then netDartShift H fuel d else 0`. -/
theorem rsstShift_eq_foldl_if_of_loopless (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u v : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false) :
    rsstShift H fuel u v =
      (getOrbit H.node fuel u).foldl
        (fun acc d => acc + if Hypermap.sameVertex H (H.edge.f d) v fuel then netDartShift H fuel d else 0) 0 := by
  rw [rsstShift_eq_filter_netDartShift H darts h_all h_le u v,
      ← foldl_add_filter (getOrbit H.node fuel u) (fun d => Hypermap.sameVertex H (H.edge.f d) v fuel) (fun d => netDartShift H fuel d)]
  cases h_uv : Hypermap.sameVertex H u v fuel with
  | false => rfl
  | true =>
    dsimp
    have h_empty : (getOrbit H.node fuel u).filter (fun d => Hypermap.sameVertex H (H.edge.f d) v fuel) = [] := by
      apply _root_.Hypermap.filter_eq_nil_of_forall_false
      intro d hd
      cases h_ev : Hypermap.sameVertex H (H.edge.f d) v fuel with
      | false => rfl
      | true =>
        have h_vu : Hypermap.sameVertex H v u fuel = true := by
          rw [sameVertex_symm_of_complete H darts h_all h_le v u]
          exact h_uv
        have h_eu : Hypermap.sameVertex H (H.edge.f d) u fuel = true :=
          sameVertex_trans_of_complete H darts h_all h_le h_ev h_vu
        rw [h_loopless d hd] at h_eu
        contradiction
    rw [h_empty]
    rfl

/-- Fubini / Swap-of-Summation Lemma for `sumShiftsTo (rsstChargeShift H fuel) u vs`:
    for any loopless vertex `u` and any vertex list `vs`, `sumShiftsTo` equals the `foldl` over `u`'s orbit
    where each dart `d` is weighted by the number of `v ∈ vs` in the orbit of `H.edge.f d`. -/
theorem sumShiftsTo_rsstChargeShift_eq_foldl_filter_length (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (vs : List H.Dart) :
    sumShiftsTo (rsstChargeShift H fuel) u vs =
      (getOrbit H.node fuel u).foldl
        (fun acc d => acc +
          ((vs.filter (fun v => Hypermap.sameVertex H (H.edge.f d) v fuel)).length : Int) * netDartShift H fuel d) 0 := by
  induction vs with
  | nil =>
    dsimp [sumShiftsTo, List.filter]
    symm
    apply foldl_add_eq_zero
    intro d _
    omega
  | cons v vs ih =>
    dsimp [sumShiftsTo]
    change rsstShift H fuel u v + sumShiftsTo (rsstChargeShift H fuel) u vs = _
    rw [rsstShift_eq_foldl_if_of_loopless H darts h_all h_le u v h_loopless, ih, ← foldl_add_add]
    apply foldl_add_congr
    intro d _
    dsimp [List.filter]
    cases Hypermap.sameVertex H (H.edge.f d) v fuel
    · simp
    · simp [Int.add_mul]
      omega

/-- Master Global-to-Local Charge Shift Bridge (`sumShiftsTo = orbitNetShift`):
    for any loopless vertex `u`, the global sum of pairwise charge shifts
    `sumShiftsTo (rsstChargeShift H fuel) u (extractGraph H darts).vertices`
    equals the local orbit sum `orbitNetShift H fuel u`. -/
theorem sumShiftsTo_rsstChargeShift_eq_orbitNetShift (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false) :
    sumShiftsTo (rsstChargeShift H fuel) u (Hypermap.extractGraph H darts).vertices =
      orbitNetShift H fuel u := by
  rw [sumShiftsTo_rsstChargeShift_eq_foldl_filter_length H darts h_all h_le u h_loopless]
  dsimp [orbitNetShift]
  apply foldl_add_congr
  intro d _
  rw [_root_.Hypermap.extractGraph_vertices_eq_canonicalOrbits_reverse H darts darts.length]
  have h_one : (((_root_.Hypermap.canonicalOrbits H.node darts.length darts).reverse).filter
      (fun v => Hypermap.sameVertex H (H.edge.f d) v fuel)).length = 1 :=
    _root_.Hypermap.filter_canonicalOrbits_reverse_length_eq_one H.node darts h_all (Nat.le_refl _) h_le (H.edge.f d)
  rw [h_one]
  omega

/-- Master Global-to-Local Final Charge Identity (`finalCharge = initialCharge + orbitNetShift`):
    for any loopless vertex `u`, `finalCharge H (rsstChargeShift H fuel) darts u`
    equals `initialCharge H u fuel + orbitNetShift H fuel u`. -/
theorem finalCharge_eq_initialCharge_add_orbitNetShift (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false) :
    finalCharge H (rsstChargeShift H fuel) darts u =
      initialCharge H u fuel + orbitNetShift H fuel u := by
  dsimp [finalCharge]
  rw [← initialCharge_fuel_eq_of_complete H darts h_all u h_le,
      sumShiftsTo_rsstChargeShift_eq_orbitNetShift H darts h_all h_le u h_loopless]

/-- Global Degree-5 Discharging Theorem:
    if `nodeDegree H u fuel = 5`, `u` has no self-loops, and every neighbor dart `H.edge.f d`
    has degree `≥ 6` (`∀ d ∈ getOrbit H.node fuel u, 6 ≤ nodeDegree H (H.edge.f d) fuel`),
    then `finalCharge H (rsstChargeShift H fuel) darts u ≤ 0`! -/
theorem finalCharge_le_zero_of_deg_5 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (h_deg5 : Hypermap.nodeDegree H u fuel = 5)
    (h_nb6 : ∀ d ∈ getOrbit H.node fuel u, 6 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    finalCharge H (rsstChargeShift H fuel) darts u ≤ 0 := by
  rw [finalCharge_eq_initialCharge_add_orbitNetShift H darts h_all h_le u h_loopless]
  exact initialCharge_add_orbitNetShift_le_zero_of_deg_5 H darts h_all h_le u
    (fun d _ => H.edge_involution d) h_deg5 h_nb6

/-- Global Degree-≥12 Discharging Theorem:
    if `12 ≤ nodeDegree H u fuel`, `u` has no self-loops, and every incoming dart `H.edge.f d`
    sends at most `5` units of charge (`∀ d ∈ getOrbit H.node fuel u, dartRuleOutflow H fuel (H.edge.f d) ≤ 5`),
    then `finalCharge H (rsstChargeShift H fuel) darts u ≤ 0`! -/
theorem finalCharge_le_zero_of_deg_ge_12 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (h_deg12 : 12 ≤ Hypermap.nodeDegree H u fuel)
    (h_in5 : ∀ d ∈ getOrbit H.node fuel u, dartRuleOutflow H fuel (H.edge.f d) ≤ 5) :
    finalCharge H (rsstChargeShift H fuel) darts u ≤ 0 := by
  rw [finalCharge_eq_initialCharge_add_orbitNetShift H darts h_all h_le u h_loopless]
  exact initialCharge_add_orbitNetShift_le_zero_of_deg_ge_12 H darts h_all h_le u h_deg12 h_in5

/-- Dual Specialization of `finalCharge = initialCharge + orbitNetShift`:
    for any bridgeless hypermap `H`, every vertex `u` of `H.dual` automatically satisfies
    `finalCharge H.dual (rsstChargeShift H.dual fuel) darts u = initialCharge H.dual u fuel + orbitNetShift H.dual fuel u`. -/
theorem dual_finalCharge_eq_initialCharge_add_orbitNetShift_of_isBridgeless (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b fuel : Nat} (h_le_b : darts.length ≤ fuel_b) (h_le : darts.length ≤ fuel)
    (h_bridge : Hypermap.isBridgeless H darts fuel_b) (u : H.Dart) :
    finalCharge H.dual (rsstChargeShift H.dual fuel) darts u =
      initialCharge H.dual u fuel + orbitNetShift H.dual fuel u :=
  finalCharge_eq_initialCharge_add_orbitNetShift H.dual darts h_all h_le u
    (dual_loopless_orbit_of_isBridgeless H darts h_all h_le_b h_le h_bridge u)

/-!
### Stage E.1: Degree-6 Discharging & Vanishing Inflow from Degree `≥ 7` to Target Degree `≤ 6`
-/

/-- Decidable rule separation between source degree `≥ 7` and target degree `≤ 6`:
    every entry `r ∈ theRules` has either `r.b0.2 ≤ 6` or `7 ≤ r.b1.1`. -/
theorem theRules_b1_ge_7_of_b0_ge_7 :
    ∀ r ∈ theRules, r.b0.2 ≤ 6 ∨ 7 ≤ r.b1.1 := by decide

/-- No rule in `theRules` matches a dart `d` from a vertex of degree `≥ 7` to a vertex of degree `≤ 6`. -/
theorem matchesRawRule_eq_false_of_deg_ge_7_of_target_deg_le_6 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (inv : Bool) (d : H.Dart) {r : RawRule} (hr : r ∈ theRules)
    (h_deg : 7 ≤ Hypermap.nodeDegree H d fuel)
    (h_tdeg : Hypermap.nodeDegree H (H.edge.f d) fuel ≤ 6) :
    matchesRawRule H fuel inv d r = false := by
  rcases theRules_b1_ge_7_of_b0_ge_7 r hr with hb0 | hb1
  · unfold matchesRawRule
    rw [ruleVertexDart_zero, degMatchesBound_eq_false_of_gt (by omega) (by omega)]
    rfl
  · unfold matchesRawRule
    rw [ruleVertexDart_one, @degMatchesBound_eq_false_of_lt (Hypermap.nodeDegree H (H.edge.f d) fuel) r.b1 (by omega) (by omega)]
    simp

/-- Outflow along dart `d` is `0` whenever `7 ≤ nodeDegree H d fuel` and `nodeDegree H (H.edge.f d) fuel ≤ 6`. -/
theorem dartRuleOutflow_eq_zero_of_deg_ge_7_of_target_deg_le_6 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_deg : 7 ≤ Hypermap.nodeDegree H d fuel)
    (h_tdeg : Hypermap.nodeDegree H (H.edge.f d) fuel ≤ 6) :
    dartRuleOutflow H fuel d = 0 := by
  dsimp [dartRuleOutflow]
  apply foldl_add_eq_zero
  intro r hr
  dsimp [rawRuleOutflow]
  rw [matchesRawRule_eq_false_of_deg_ge_7_of_target_deg_le_6 H fuel false d hr h_deg h_tdeg,
      matchesRawRule_eq_false_of_deg_ge_7_of_target_deg_le_6 H fuel true d hr h_deg h_tdeg]
  simp

/-- No vertex `u` of degree `≥ 7` sends any charge to a vertex `v` of degree `≤ 6`. -/
theorem vertexRuleOutflow_eq_zero_of_deg_ge_7_of_target_deg_le_6 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u v : H.Dart)
    (h_u : 7 ≤ Hypermap.nodeDegree H u fuel)
    (h_v : Hypermap.nodeDegree H v fuel ≤ 6) :
    vertexRuleOutflow H fuel u v = 0 := by
  dsimp [vertexRuleOutflow]
  split
  · rfl
  · apply foldl_add_eq_zero
    intro d hd
    have hd_orb : d ∈ getOrbit H.node fuel u := (List.mem_filter.mp hd).1
    have hd_same : Hypermap.sameVertex H (H.edge.f d) v fuel = true := (List.mem_filter.mp hd).2
    have hd_deg : 7 ≤ Hypermap.nodeDegree H d fuel := by
      have := nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hd_orb
      omega
    have hed_deg : Hypermap.nodeDegree H (H.edge.f d) fuel ≤ 6 := by
      have := nodeDegree_eq_of_sameVertex H darts h_all h_le hd_same
      omega
    exact dartRuleOutflow_eq_zero_of_deg_ge_7_of_target_deg_le_6 H fuel d hd_deg hed_deg

/-- When `nodeDegree H d fuel ≤ 6` and `7 ≤ nodeDegree H (H.edge.f d) fuel` (with `H.edge.f (H.edge.f d) = d`),
    inflow along `H.edge.f d` is `0`, so `netDartShift H fuel d = - dartRuleOutflow H fuel d ≤ 0`. -/
theorem netDartShift_eq_neg_outflow_of_deg_le_6_of_target_deg_ge_7 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_inv : H.edge.f (H.edge.f d) = d)
    (h_d : Hypermap.nodeDegree H d fuel ≤ 6)
    (h_ed : 7 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    netDartShift H fuel d = - dartRuleOutflow H fuel d := by
  dsimp [netDartShift]
  have h_in : dartRuleOutflow H fuel (H.edge.f d) = 0 := by
    apply dartRuleOutflow_eq_zero_of_deg_ge_7_of_target_deg_le_6 H fuel (H.edge.f d) h_ed
    rw [h_inv]
    exact h_d
  omega

/-- Every vertex of degree `6` has `initialCharge = 0`. -/
theorem initialCharge_eq_zero_of_deg_6 (H : Hypermap) [DecidableEq H.Dart]
    (u : H.Dart) (fuel : Nat) (h_deg6 : Hypermap.nodeDegree H u fuel = 6) :
    initialCharge H u fuel = 0 := by
  dsimp [initialCharge]
  omega

/-- For any loopless degree-6 vertex `u`, `finalCharge H (rsstChargeShift H fuel) darts u = orbitNetShift H fuel u`. -/
theorem finalCharge_eq_orbitNetShift_of_deg_6 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (h_deg6 : Hypermap.nodeDegree H u fuel = 6) :
    finalCharge H (rsstChargeShift H fuel) darts u = orbitNetShift H fuel u := by
  rw [finalCharge_eq_initialCharge_add_orbitNetShift H darts h_all h_le u h_loopless,
      initialCharge_eq_zero_of_deg_6 H u fuel h_deg6]
  omega

/-- For any loopless degree-6 vertex `u` with `orbitNetShift H fuel u ≤ 0`, `finalCharge ≤ 0`. -/
theorem finalCharge_le_zero_of_deg_6_of_orbitNetShift_nonpos (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (h_deg6 : Hypermap.nodeDegree H u fuel = 6)
    (h_net : orbitNetShift H fuel u ≤ 0) :
    finalCharge H (rsstChargeShift H fuel) darts u ≤ 0 := by
  rw [finalCharge_eq_orbitNetShift_of_deg_6 H darts h_all h_le u h_loopless h_deg6]
  exact h_net

/-- Global Degree-6 Discharging Theorem (when all neighbors have degree `≥ 7`):
    any loopless degree-6 vertex `u` whose neighbors all have degree `≥ 7` satisfies `finalCharge ≤ 0`. -/
theorem finalCharge_le_zero_of_deg_6_of_neighbors_deg_ge_7 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (h_deg6 : Hypermap.nodeDegree H u fuel = 6)
    (h_nb7 : ∀ d ∈ getOrbit H.node fuel u, 7 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    finalCharge H (rsstChargeShift H fuel) darts u ≤ 0 := by
  apply finalCharge_le_zero_of_deg_6_of_orbitNetShift_nonpos H darts h_all h_le u h_loopless h_deg6
  dsimp [orbitNetShift]
  have h_le_c := foldl_add_le_of_le_const (getOrbit H.node fuel u) (fun d => netDartShift H fuel d) 0 (by
    intro d hd
    have hd_deg : Hypermap.nodeDegree H d fuel ≤ 6 := by
      have := nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hd
      omega
    dsimp
    rw [netDartShift_eq_neg_outflow_of_deg_le_6_of_target_deg_ge_7 H fuel d (H.edge_involution d) hd_deg (h_nb7 d hd)]
    have h_nonneg := dartRuleOutflow_nonneg H fuel d
    omega)
  dsimp at h_le_c
  omega

/-! ### Checkpoint E.2: Mutual-Exclusion Per-Dart Outflow Upper Bounds (`deg(d) ∈ {5, 6, 7, 8}`) -/

private def r1  : RawRule := { num := 1,  b0 := (5, 5), b1 := (5, 12), triples := [], invert := true }
private def r3  : RawRule := { num := 3,  b0 := (5, 6), b1 := (7, 12), triples := [(3, (5, 5))], invert := true }
private def r5  : RawRule := { num := 5,  b0 := (5, 6), b1 := (6, 12), triples := [(3, (5, 6)), (5, (5, 5))], invert := true }
private def r7  : RawRule := { num := 7,  b0 := (6, 6), b1 := (6, 12), triples := [(3, (5, 5)), (5, (5, 6)), (9, (5, 5))], invert := true }
private def r9  : RawRule := { num := 9,  b0 := (6, 6), b1 := (6, 12), triples := [(3, (6, 6)), (5, (5, 6)), (9, (5, 5))], invert := true }
private def r11 : RawRule := { num := 11, b0 := (6, 6), b1 := (6, 12), triples := [(3, (6, 6)), (5, (6, 6)), (9, (5, 6)), (11, (5, 5))], invert := true }
private def r13 : RawRule := { num := 13, b0 := (6, 6), b1 := (7, 12), triples := [(3, (5, 5)), (5, (6, 6)), (7, (5, 5)), (9, (5, 6))], invert := true }
private def r15 : RawRule := { num := 15, b0 := (6, 6), b1 := (7, 12), triples := [(3, (6, 6)), (5, (6, 6)), (7, (5, 5)), (9, (6, 6)), (11, (5, 6))], invert := true }
private def r17 : RawRule := { num := 17, b0 := (7, 7), b1 := (7, 12), triples := [(3, (5, 6)), (5, (5, 5))], invert := true }
private def r19 : RawRule := { num := 19, b0 := (7, 7), b1 := (7, 12), triples := [(3, (5, 6)), (5, (5, 6)), (14, (5, 5))], invert := true }
private def r21 : RawRule := { num := 21, b0 := (7, 7), b1 := (7, 12), triples := [(2, (5, 5)), (3, (5, 5)), (4, (5, 5)), (5, (5, 5))], invert := false }
private def r22 : RawRule := { num := 22, b0 := (7, 7), b1 := (7, 12), triples := [(2, (5, 5)), (3, (5, 5)), (4, (5, 5)), (5, (6, 12))], invert := true }
private def r24 : RawRule := { num := 24, b0 := (7, 7), b1 := (7, 12), triples := [(2, (5, 5)), (3, (5, 5)), (4, (6, 6)), (5, (6, 12)), (8, (5, 5))], invert := true }
private def r26 : RawRule := { num := 26, b0 := (7, 7), b1 := (7, 12), triples := [(2, (5, 5)), (3, (5, 5)), (4, (5, 5)), (5, (5, 5)), (8, (5, 5)), (9, (5, 5))], invert := false }
private def r27 : RawRule := { num := 27, b0 := (7, 7), b1 := (8, 12), triples := [(2, (5, 5)), (3, (5, 5)), (4, (6, 6)), (5, (5, 5)), (6, (5, 5)), (8, (5, 5))], invert := true }
private def r29 : RawRule := { num := 29, b0 := (7, 7), b1 := (7, 12), triples := [(2, (6, 6)), (3, (5, 5)), (4, (5, 5)), (8, (5, 5))], invert := true }
private def r31 : RawRule := { num := 31, b0 := (7, 7), b1 := (7, 12), triples := [(2, (6, 6)), (3, (5, 5)), (4, (5, 5)), (5, (7, 12)), (12, (6, 6)), (13, (5, 5))], invert := true }
private def r33 : RawRule := { num := 33, b0 := (7, 7), b1 := (7, 12), triples := [(2, (6, 6)), (3, (5, 5)), (4, (6, 6)), (5, (5, 5)), (12, (6, 6)), (13, (5, 5))], invert := true }
private def r35 : RawRule := { num := 35, b0 := (7, 7), b1 := (7, 12), triples := [(2, (6, 6)), (3, (5, 5)), (4, (5, 5)), (5, (5, 5)), (8, (6, 6)), (12, (5, 5)), (13, (7, 12))], invert := true }
private def r39 : RawRule := { num := 39, b0 := (7, 7), b1 := (8, 12), triples := [(2, (6, 12)), (3, (5, 5)), (4, (6, 6)), (5, (6, 6)), (7, (5, 5)), (9, (5, 5)), (12, (6, 6)), (13, (5, 5))], invert := true }
private def r41 : RawRule := { num := 41, b0 := (7, 7), b1 := (7, 12), triples := [(2, (6, 6)), (3, (6, 6)), (4, (5, 5)), (5, (6, 6)), (12, (5, 5)), (13, (5, 5))], invert := true }
private def r47 : RawRule := { num := 47, b0 := (7, 7), b1 := (7, 12), triples := [(2, (5, 5)), (3, (7, 7)), (5, (5, 5)), (9, (5, 5))], invert := true }
private def r51 : RawRule := { num := 51, b0 := (7, 7), b1 := (7, 12), triples := [(2, (5, 5)), (3, (7, 7)), (4, (5, 5)), (5, (5, 5)), (9, (6, 6)), (11, (5, 5)), (14, (5, 5))], invert := true }
private def r57 : RawRule := { num := 57, b0 := (8, 8), b1 := (7, 12), triples := [(2, (5, 5)), (3, (5, 5)), (4, (5, 5)), (5, (5, 5)), (12, (5, 5))], invert := true }
private def r59 : RawRule := { num := 59, b0 := (8, 8), b1 := (7, 12), triples := [(2, (5, 5)), (3, (5, 5)), (4, (5, 5)), (8, (5, 5)), (12, (5, 5)), (13, (5, 5))], invert := true }
private def r61 : RawRule := { num := 61, b0 := (8, 8), b1 := (7, 12), triples := [(2, (5, 5)), (3, (5, 5)), (4, (5, 5)), (5, (6, 6)), (9, (5, 5)), (14, (5, 5))], invert := true }
private def r63 : RawRule := { num := 63, b0 := (8, 8), b1 := (7, 12), triples := [(2, (5, 5)), (3, (5, 5)), (4, (5, 5)), (5, (5, 5)), (8, (5, 5)), (9, (5, 5)), (12, (6, 12)), (14, (6, 12))], invert := false }
private def r64 : RawRule := { num := 64, b0 := (8, 8), b1 := (7, 12), triples := [(2, (5, 5)), (3, (5, 5)), (4, (5, 5)), (5, (5, 5)), (8, (5, 5)), (9, (6, 12)), (12, (6, 12)), (14, (6, 12))], invert := true }

/-- Pure degree-vector evaluator for `matchesRawRule`: checks whether degree vector `degs : Nat → Nat`
    satisfies `r.b0` at `0`, `r.b1` at `1`, and all `(k, b) ∈ r.triples` at `k`. -/
def matchesRawRuleDegs (degs : Nat → Nat) (r : RawRule) : Bool :=
  degMatchesBound (degs 0) r.b0 &&
  degMatchesBound (degs 1) r.b1 &&
  r.triples.all (fun p => degMatchesBound (degs p.1) p.2)

/-- `matchesRawRule H fuel inv d r` is definitionally equal to `matchesRawRuleDegs`
    applied to the local degree vector `fun k => Hypermap.nodeDegree H (ruleVertexDart H inv d k) fuel`. -/
theorem matchesRawRule_eq_matchesRawRuleDegs (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (inv : Bool) (d : H.Dart) (r : RawRule) :
    matchesRawRule H fuel inv d r =
      matchesRawRuleDegs (fun k => Hypermap.nodeDegree H (ruleVertexDart H inv d k) fuel) r := rfl

/-- Single-orientation rule outflow for a pure degree vector `degs : Nat → Nat`. -/
def orientOutflowDegs (inv : Bool) (degs : Nat → Nat) : Int :=
  theRules.foldl (fun acc r => acc + if (if inv then r.invert else true) && matchesRawRuleDegs degs r then 1 else 0) 0

/-- `dartRuleOutflow H fuel d` decomposes into the sum of `orientOutflowDegs false` and `orientOutflowDegs true`. -/
theorem dartRuleOutflow_eq_orientOutflowDegs_add (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart) :
    dartRuleOutflow H fuel d =
      orientOutflowDegs false (fun k => Hypermap.nodeDegree H (ruleVertexDart H false d k) fuel) +
      orientOutflowDegs true (fun k => Hypermap.nodeDegree H (ruleVertexDart H true d k) fuel) := by
  dsimp [dartRuleOutflow, orientOutflowDegs, matchesRawRuleDegs, matchesRawRule]
  rw [← foldl_add_add]
  rfl

/-- Active-rule filter predicate for source degree `b0_deg` and minimum target degree `min_b1`. -/
def ruleActiveFor (b0_deg : Nat) (min_b1 : Nat) (r : RawRule) : Bool :=
  let upp1 := if r.b1.2 == 9 then 12 else r.b1.2
  degMatchesBound b0_deg r.b0 && (decide (upp1 == 12) || decide (min_b1 ≤ upp1))

/-- Filtering `theRules` by `ruleActiveFor b0_deg min_b1` preserves `orientOutflowDegs`
    whenever `degs 0 = b0_deg` and `min_b1 ≤ degs 1`. -/
theorem orientOutflowDegs_eq_filter_active (inv : Bool) (degs : Nat → Nat)
    (b0_deg min_b1 : Nat) (hb0 : degs 0 = b0_deg) (hb1 : min_b1 ≤ degs 1) :
    orientOutflowDegs inv degs =
      (theRules.filter (ruleActiveFor b0_deg min_b1)).foldl
        (fun acc r => acc + if (if inv then r.invert else true) && matchesRawRuleDegs degs r then 1 else 0) 0 := by
  dsimp [orientOutflowDegs]
  rw [foldl_add_filter]
  apply foldl_add_congr
  intro r _
  cases h_act : ruleActiveFor b0_deg min_b1 r
  · dsimp [ruleActiveFor] at h_act
    dsimp [matchesRawRuleDegs]
    rw [hb0]
    cases h0 : degMatchesBound b0_deg r.b0
    · simp
    · simp only [h0, Bool.true_and, Bool.or_eq_false_iff, decide_eq_false_iff_not] at h_act ⊢
      have h1 : degMatchesBound (degs 1) r.b1 = false := by
        dsimp [degMatchesBound]
        have h_n12 : ¬ ((if r.b1.2 == 9 then 12 else r.b1.2) == 12) := h_act.1
        have h_nle : ¬ (min_b1 ≤ if r.b1.2 == 9 then 12 else r.b1.2) := h_act.2
        have h_ndeg : ¬ (degs 1 ≤ if r.b1.2 == 9 then 12 else r.b1.2) := by omega
        rw [decide_eq_false h_n12, decide_eq_false h_ndeg]
        simp
      simp [h1]
  · simp

private theorem all_eq_false_of_mem {α : Type} (l : List α) (p : α → Bool) {x : α}
    (hx : x ∈ l) (hp : p x = false) : l.all p = false := by
  induction l with
  | nil => contradiction
  | cons a as ih =>
    dsimp [List.all]
    rcases List.mem_cons.mp hx with rfl | hmem
    · rw [hp]; rfl
    · rw [ih hmem]; simp

/-- If `(k, (lo, hi)) ∈ r.triples`, `0 < lo`, and `degs k < lo`, then `matchesRawRuleDegs degs r = false`. -/
theorem not_matchesRawRuleDegs_of_triple_lt (degs : Nat → Nat) (r : RawRule)
    (k lo hi : Nat) (h_mem : (k, (lo, hi)) ∈ r.triples) (h_pos : 0 < lo) (h_lt : degs k < lo) :
    matchesRawRuleDegs degs r = false := by
  dsimp [matchesRawRuleDegs]
  have h_all : r.triples.all (fun p => degMatchesBound (degs p.1) p.2) = false :=
    all_eq_false_of_mem r.triples (fun p => degMatchesBound (degs p.1) p.2) h_mem
      (@degMatchesBound_eq_false_of_lt (degs k) (lo, hi) h_pos h_lt)
  simp [h_all]

/-- If `(k, (lo, hi)) ∈ r.triples`, `hi ≤ 8`, and `hi < degs k`, then `matchesRawRuleDegs degs r = false`. -/
theorem not_matchesRawRuleDegs_of_triple_gt (degs : Nat → Nat) (r : RawRule)
    (k lo hi : Nat) (h_mem : (k, (lo, hi)) ∈ r.triples) (h_hi : hi ≤ 8) (h_gt : hi < degs k) :
    matchesRawRuleDegs degs r = false := by
  dsimp [matchesRawRuleDegs]
  have h_all : r.triples.all (fun p => degMatchesBound (degs p.1) p.2) = false :=
    all_eq_false_of_mem r.triples (fun p => degMatchesBound (degs p.1) p.2) h_mem
      (@degMatchesBound_eq_false_of_gt (degs k) (lo, hi) h_hi h_gt)
  simp [h_all]

/-- Two rules `rA` and `rB` with disjoint degree intervals `[loA, hiA]` and `[loB, hiB]` (`hiA ≤ 8`, `hiA < loB`)
    at coordinate `k` cannot both fire on the same degree vector `degs`. -/
theorem conflict_pair_at (inv : Bool) (degs : Nat → Nat) (rA rB : RawRule)
    (k loA hiA loB hiB : Nat)
    (hA : (k, (loA, hiA)) ∈ rA.triples) (hB : (k, (loB, hiB)) ∈ rB.triples)
    (h_hiA : hiA ≤ 8) (h_sep : hiA < loB) :
    (if (if inv then rA.invert else true) && matchesRawRuleDegs degs rA then (1 : Int) else 0) +
    (if (if inv then rB.invert else true) && matchesRawRuleDegs degs rB then (1 : Int) else 0) ≤ 1 := by
  by_cases hk : degs k ≤ hiA
  · have hB_false : matchesRawRuleDegs degs rB = false :=
      not_matchesRawRuleDegs_of_triple_lt degs rB k loB hiB hB (by omega) (by omega)
    rw [hB_false]; simp
    split <;> omega
  · have hA_false : matchesRawRuleDegs degs rA = false :=
      not_matchesRawRuleDegs_of_triple_gt degs rA k loA hiA hA h_hiA (by omega)
    rw [hA_false]; simp
    split <;> omega

private theorem if_false_eq_true_zero : (if false = true then (1 : Int) else 0) = 0 := rfl

/-- For `degs 0 = 5`, at most 3 rules (`r1, r3, r5`) can match in each orientation. -/
theorem orientOutflowDegs_le_3_of_deg_5 (inv : Bool) (degs : Nat → Nat) (hb0 : degs 0 = 5) :
    orientOutflowDegs inv degs ≤ 3 := by
  rw [orientOutflowDegs_eq_filter_active inv degs 5 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 5 0) = [r1, r3, r5] := rfl
  rw [h_filt]
  dsimp only [List.foldl]
  have h1 : (if (if inv then r1.invert else true) && matchesRawRuleDegs degs r1 then (1 : Int) else 0) ≤ 1 := by split <;> omega
  have h3 : (if (if inv then r3.invert else true) && matchesRawRuleDegs degs r3 then (1 : Int) else 0) ≤ 1 := by split <;> omega
  have h5 : (if (if inv then r5.invert else true) && matchesRawRuleDegs degs r5 then (1 : Int) else 0) ≤ 1 := by split <;> omega
  omega

/-- Any dart `d` at a degree-5 vertex sends at most `6` units of rule outflow (`≤ 3` per orientation). -/
theorem dartRuleOutflow_le_6_of_deg_5 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart) (h_d : Hypermap.nodeDegree H d fuel = 5) :
    dartRuleOutflow H fuel d ≤ 6 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have hf := orientOutflowDegs_le_3_of_deg_5 false (fun k => Hypermap.nodeDegree H (ruleVertexDart H false d k) fuel) (by simpa using h_d)
  have ht := orientOutflowDegs_le_3_of_deg_5 true (fun k => Hypermap.nodeDegree H (ruleVertexDart H true d k) fuel) (by simpa using h_d)
  omega

/-- For `degs 0 = 6`, the 7 candidate rules `[r3, r5, r7, r9, r11, r13, r15]` partition into
    3 mutually exclusive cliques (`{r3, r11}`, `{r5, r13}`, `{r7, r9, r15}`), so at most 3 match per orientation. -/
theorem orientOutflowDegs_le_3_of_deg_6 (inv : Bool) (degs : Nat → Nat) (hb0 : degs 0 = 6) :
    orientOutflowDegs inv degs ≤ 3 := by
  rw [orientOutflowDegs_eq_filter_active inv degs 6 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 6 0) = [r3, r5, r7, r9, r11, r13, r15] := rfl
  rw [h_filt]
  dsimp only [List.foldl]
  have hc1 := conflict_pair_at inv degs r3 r11 3 5 5 6 6 (by decide) (by decide) (by decide) (by decide)
  have hc2 := conflict_pair_at inv degs r5 r13 5 5 5 6 6 (by decide) (by decide) (by decide) (by decide)
  have hc3 : (if (if inv then r7.invert else true) && matchesRawRuleDegs degs r7 then (1 : Int) else 0) +
             (if (if inv then r9.invert else true) && matchesRawRuleDegs degs r9 then (1 : Int) else 0) +
             (if (if inv then r15.invert else true) && matchesRawRuleDegs degs r15 then (1 : Int) else 0) ≤ 1 := by
    by_cases h3 : degs 3 ≤ 5
    · have h9 : matchesRawRuleDegs degs r9 = false :=
        not_matchesRawRuleDegs_of_triple_lt degs r9 3 6 6 (by decide) (by decide) (by omega)
      have h15 : matchesRawRuleDegs degs r15 = false :=
        not_matchesRawRuleDegs_of_triple_lt degs r15 3 6 6 (by decide) (by decide) (by omega)
      rw [h9, h15]; simp; split <;> omega
    · have h7 : matchesRawRuleDegs degs r7 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r7 3 5 5 (by decide) (by decide) (by omega)
      have hc9_15 := conflict_pair_at inv degs r9 r15 9 5 5 6 6 (by decide) (by decide) (by decide) (by decide)
      rw [h7]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
  omega

/-- Any dart `d` at a degree-6 vertex sends at most `6` units of rule outflow (`≤ 3` per orientation). -/
theorem dartRuleOutflow_le_6_of_deg_6 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart) (h_d : Hypermap.nodeDegree H d fuel = 6) :
    dartRuleOutflow H fuel d ≤ 6 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have hf := orientOutflowDegs_le_3_of_deg_6 false (fun k => Hypermap.nodeDegree H (ruleVertexDart H false d k) fuel) (by simpa using h_d)
  have ht := orientOutflowDegs_le_3_of_deg_6 true (fun k => Hypermap.nodeDegree H (ruleVertexDart H true d k) fuel) (by simpa using h_d)
  omega

/-- For `degs 0 = 8` and `8 ≤ degs 1`, the 5 candidate rules `[r57, r59, r61, r63, r64]`
    contribute at most `2` per orientation. -/
theorem orientOutflowDegs_le_2_of_deg_8_of_target_deg_ge_8 (inv : Bool) (degs : Nat → Nat)
    (hb0 : degs 0 = 8) (hb1 : 8 ≤ degs 1) :
    orientOutflowDegs inv degs ≤ 2 := by
  rw [orientOutflowDegs_eq_filter_active inv degs 8 8 hb0 hb1]
  have h_filt : theRules.filter (ruleActiveFor 8 8) = [r57, r59, r61, r63, r64] := rfl
  rw [h_filt]
  dsimp only [List.foldl]
  by_cases h12 : degs 12 ≤ 5
  · have h63 : matchesRawRuleDegs degs r63 = false :=
      not_matchesRawRuleDegs_of_triple_lt degs r63 12 6 12 (by decide) (by decide) (by omega)
    have h64 : matchesRawRuleDegs degs r64 = false :=
      not_matchesRawRuleDegs_of_triple_lt degs r64 12 6 12 (by decide) (by decide) (by omega)
    have hc57_61 := conflict_pair_at inv degs r57 r61 5 5 5 6 6 (by decide) (by decide) (by decide) (by decide)
    have h59 : (if (if inv then r59.invert else true) && matchesRawRuleDegs degs r59 then (1 : Int) else 0) ≤ 1 := by split <;> omega
    rw [h63, h64]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
  · have h57 : matchesRawRuleDegs degs r57 = false :=
      not_matchesRawRuleDegs_of_triple_gt degs r57 12 5 5 (by decide) (by decide) (by omega)
    have h59 : matchesRawRuleDegs degs r59 = false :=
      not_matchesRawRuleDegs_of_triple_gt degs r59 12 5 5 (by decide) (by decide) (by omega)
    have hc63_64 := conflict_pair_at inv degs r63 r64 9 5 5 6 12 (by decide) (by decide) (by decide) (by decide)
    have h61 : (if (if inv then r61.invert else true) && matchesRawRuleDegs degs r61 then (1 : Int) else 0) ≤ 1 := by split <;> omega
    rw [h57, h59]; simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- Any dart `d` from a degree-8 vertex to a vertex of degree `≥ 8` sends at most `4` units of rule outflow. -/
theorem dartRuleOutflow_le_4_of_deg_8_of_target_deg_ge_8 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_d : Hypermap.nodeDegree H d fuel = 8)
    (h_ed : 8 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    dartRuleOutflow H fuel d ≤ 4 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have hf := orientOutflowDegs_le_2_of_deg_8_of_target_deg_ge_8 false
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H false d k) fuel) (by simpa using h_d) (by simpa using h_ed)
  have ht := orientOutflowDegs_le_2_of_deg_8_of_target_deg_ge_8 true
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H true d k) fuel) (by simpa using h_d) (by simpa using h_ed)
  omega

/-- Clique 1 for `(b0 = 7, b1 ≥ 8)`: among `{r17, r22, r24, r31, r39, r41, r47}`, at most `1` rule can match. -/
private theorem deg7_b1_ge_8_clique1_le_1 (inv : Bool) (degs : Nat → Nat) :
    (if (if inv then r17.invert else true) && matchesRawRuleDegs degs r17 then (1 : Int) else 0) +
    (if (if inv then r22.invert else true) && matchesRawRuleDegs degs r22 then (1 : Int) else 0) +
    (if (if inv then r24.invert else true) && matchesRawRuleDegs degs r24 then (1 : Int) else 0) +
    (if (if inv then r31.invert else true) && matchesRawRuleDegs degs r31 then (1 : Int) else 0) +
    (if (if inv then r39.invert else true) && matchesRawRuleDegs degs r39 then (1 : Int) else 0) +
    (if (if inv then r41.invert else true) && matchesRawRuleDegs degs r41 then (1 : Int) else 0) +
    (if (if inv then r47.invert else true) && matchesRawRuleDegs degs r47 then (1 : Int) else 0) ≤ 1 := by
  by_cases h5 : degs 5 ≤ 5
  · have h22 : matchesRawRuleDegs degs r22 = false :=
      not_matchesRawRuleDegs_of_triple_lt degs r22 5 6 12 (by decide) (by decide) (by omega)
    have h24 : matchesRawRuleDegs degs r24 = false :=
      not_matchesRawRuleDegs_of_triple_lt degs r24 5 6 12 (by decide) (by decide) (by omega)
    have h31 : matchesRawRuleDegs degs r31 = false :=
      not_matchesRawRuleDegs_of_triple_lt degs r31 5 7 12 (by decide) (by decide) (by omega)
    have h39 : matchesRawRuleDegs degs r39 = false :=
      not_matchesRawRuleDegs_of_triple_lt degs r39 5 6 6 (by decide) (by decide) (by omega)
    have h41 : matchesRawRuleDegs degs r41 = false :=
      not_matchesRawRuleDegs_of_triple_lt degs r41 5 6 6 (by decide) (by decide) (by omega)
    have hc17_47 := conflict_pair_at inv degs r17 r47 3 5 6 7 7 (by decide) (by decide) (by decide) (by decide)
    rw [h22, h24, h31, h39, h41]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
  · have h17 : matchesRawRuleDegs degs r17 = false :=
      not_matchesRawRuleDegs_of_triple_gt degs r17 5 5 5 (by decide) (by decide) (by omega)
    have h47 : matchesRawRuleDegs degs r47 = false :=
      not_matchesRawRuleDegs_of_triple_gt degs r47 5 5 5 (by decide) (by decide) (by omega)
    rw [h17, h47]
    by_cases h2 : degs 2 ≤ 5
    · have h31 : matchesRawRuleDegs degs r31 = false :=
        not_matchesRawRuleDegs_of_triple_lt degs r31 2 6 6 (by decide) (by decide) (by omega)
      have h39 : matchesRawRuleDegs degs r39 = false :=
        not_matchesRawRuleDegs_of_triple_lt degs r39 2 6 12 (by decide) (by decide) (by omega)
      have h41 : matchesRawRuleDegs degs r41 = false :=
        not_matchesRawRuleDegs_of_triple_lt degs r41 2 6 6 (by decide) (by decide) (by omega)
      have hc22_24 := conflict_pair_at inv degs r22 r24 4 5 5 6 6 (by decide) (by decide) (by decide) (by decide)
      rw [h31, h39, h41]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
    · have h22 : matchesRawRuleDegs degs r22 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r22 2 5 5 (by decide) (by decide) (by omega)
      have h24 : matchesRawRuleDegs degs r24 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r24 2 5 5 (by decide) (by decide) (by omega)
      rw [h22, h24]
      by_cases h4 : degs 4 ≤ 5
      · have h39 : matchesRawRuleDegs degs r39 = false :=
          not_matchesRawRuleDegs_of_triple_lt degs r39 4 6 6 (by decide) (by decide) (by omega)
        have hc31_41 := conflict_pair_at inv degs r31 r41 3 5 5 6 6 (by decide) (by decide) (by decide) (by decide)
        rw [h39]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
      · have h31 : matchesRawRuleDegs degs r31 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r31 4 5 5 (by decide) (by decide) (by omega)
        have h41 : matchesRawRuleDegs degs r41 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r41 4 5 5 (by decide) (by decide) (by omega)
        have h39 : (if (if inv then r39.invert else true) && matchesRawRuleDegs degs r39 then (1 : Int) else 0) ≤ 1 := by split <;> omega
        rw [h31, h41]; simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- Clique 3 for `(b0 = 7, b1 ≥ 8)`: among `{r26, r27, r29, r33, r35}`, at most `1` rule can match. -/
private theorem deg7_b1_ge_8_clique3_le_1 (inv : Bool) (degs : Nat → Nat) :
    (if (if inv then r26.invert else true) && matchesRawRuleDegs degs r26 then (1 : Int) else 0) +
    (if (if inv then r27.invert else true) && matchesRawRuleDegs degs r27 then (1 : Int) else 0) +
    (if (if inv then r29.invert else true) && matchesRawRuleDegs degs r29 then (1 : Int) else 0) +
    (if (if inv then r33.invert else true) && matchesRawRuleDegs degs r33 then (1 : Int) else 0) +
    (if (if inv then r35.invert else true) && matchesRawRuleDegs degs r35 then (1 : Int) else 0) ≤ 1 := by
  by_cases h2 : degs 2 ≤ 5
  · have h29 : matchesRawRuleDegs degs r29 = false :=
      not_matchesRawRuleDegs_of_triple_lt degs r29 2 6 6 (by decide) (by decide) (by omega)
    have h33 : matchesRawRuleDegs degs r33 = false :=
      not_matchesRawRuleDegs_of_triple_lt degs r33 2 6 6 (by decide) (by decide) (by omega)
    have h35 : matchesRawRuleDegs degs r35 = false :=
      not_matchesRawRuleDegs_of_triple_lt degs r35 2 6 6 (by decide) (by decide) (by omega)
    have hc26_27 := conflict_pair_at inv degs r26 r27 4 5 5 6 6 (by decide) (by decide) (by decide) (by decide)
    rw [h29, h33, h35]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
  · have h26 : matchesRawRuleDegs degs r26 = false :=
      not_matchesRawRuleDegs_of_triple_gt degs r26 2 5 5 (by decide) (by decide) (by omega)
    have h27 : matchesRawRuleDegs degs r27 = false :=
      not_matchesRawRuleDegs_of_triple_gt degs r27 2 5 5 (by decide) (by decide) (by omega)
    rw [h26, h27]
    by_cases h4 : degs 4 ≤ 5
    · have h33 : matchesRawRuleDegs degs r33 = false :=
        not_matchesRawRuleDegs_of_triple_lt degs r33 4 6 6 (by decide) (by decide) (by omega)
      have hc29_35 := conflict_pair_at inv degs r29 r35 8 5 5 6 6 (by decide) (by decide) (by decide) (by decide)
      rw [h33]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
    · have h29 : matchesRawRuleDegs degs r29 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r29 4 5 5 (by decide) (by decide) (by omega)
      have h35 : matchesRawRuleDegs degs r35 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r35 4 5 5 (by decide) (by decide) (by omega)
      have h33 : (if (if inv then r33.invert else true) && matchesRawRuleDegs degs r33 then (1 : Int) else 0) ≤ 1 := by split <;> omega
      rw [h29, h35]; simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- For `degs 0 = 7` and `8 ≤ degs 1`, at most `4` rules match in the uninverted (`inv = false`) orientation. -/
theorem orientOutflowDegs_false_le_4_of_deg_7_of_target_deg_ge_8 (degs : Nat → Nat)
    (hb0 : degs 0 = 7) (hb1 : 8 ≤ degs 1) :
    orientOutflowDegs false degs ≤ 4 := by
  rw [orientOutflowDegs_eq_filter_active false degs 7 8 hb0 hb1]
  have h_filt : theRules.filter (ruleActiveFor 7 8) =
    [r17, r19, r21, r22, r24, r26, r27, r29, r31, r33, r35, r39, r41, r47, r51] := rfl
  rw [h_filt]
  dsimp only [List.foldl]
  have hc1 := deg7_b1_ge_8_clique1_le_1 false degs
  have hc2 := conflict_pair_at false degs r19 r51 3 5 6 7 7 (by decide) (by decide) (by decide) (by decide)
  have hc3 := deg7_b1_ge_8_clique3_le_1 false degs
  have hc4 : (if (if false then r21.invert else true) && matchesRawRuleDegs degs r21 then (1 : Int) else 0) ≤ 1 := by split <;> omega
  omega

/-- For `degs 0 = 7` and `8 ≤ degs 1`, at most `3` rules match in the inverted (`inv = true`) orientation
    (since `r21.invert = false`). -/
theorem orientOutflowDegs_true_le_3_of_deg_7_of_target_deg_ge_8 (degs : Nat → Nat)
    (hb0 : degs 0 = 7) (hb1 : 8 ≤ degs 1) :
    orientOutflowDegs true degs ≤ 3 := by
  rw [orientOutflowDegs_eq_filter_active true degs 7 8 hb0 hb1]
  have h_filt : theRules.filter (ruleActiveFor 7 8) =
    [r17, r19, r21, r22, r24, r26, r27, r29, r31, r33, r35, r39, r41, r47, r51] := rfl
  rw [h_filt]
  dsimp only [List.foldl]
  have hc1 := deg7_b1_ge_8_clique1_le_1 true degs
  have hc2 := conflict_pair_at true degs r19 r51 3 5 6 7 7 (by decide) (by decide) (by decide) (by decide)
  have hc3 := deg7_b1_ge_8_clique3_le_1 true degs
  have hc4 : (if (if true then r21.invert else true) && matchesRawRuleDegs degs r21 then (1 : Int) else 0) = 0 := by
    have : r21.invert = false := rfl
    rw [this]; simp
  omega

/-- Any dart `d` from a degree-7 vertex to a vertex of degree `≥ 8` sends at most `7` units of rule outflow
    (`≤ 4` uninverted + `≤ 3` inverted). -/
theorem dartRuleOutflow_le_7_of_deg_7_of_target_deg_ge_8 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_d : Hypermap.nodeDegree H d fuel = 7)
    (h_ed : 8 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    dartRuleOutflow H fuel d ≤ 7 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have hf := orientOutflowDegs_false_le_4_of_deg_7_of_target_deg_ge_8
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H false d k) fuel) (by simpa using h_d) (by simpa using h_ed)
  have ht := orientOutflowDegs_true_le_3_of_deg_7_of_target_deg_ge_8
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H true d k) fuel) (by simpa using h_d) (by simpa using h_ed)
  omega

/-- Universal Per-Dart Inflow Bound into Degree `≥ 8`:
    for ANY dart `d` (regardless of source degree `nodeDegree H d fuel`) whose target `H.edge.f d`
    has degree `≥ 8`, `dartRuleOutflow H fuel d ≤ 7`. -/
theorem dartRuleOutflow_le_7_of_target_deg_ge_8 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_ed : 8 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    dartRuleOutflow H fuel d ≤ 7 := by
  rcases Nat.lt_or_ge (Hypermap.nodeDegree H d fuel) 5 with hlt5 | hge5
  · have := dartRuleOutflow_eq_zero_of_deg_lt_5 H fuel d hlt5; omega
  · rcases Nat.lt_or_ge 8 (Hypermap.nodeDegree H d fuel) with hgt8 | hle8
    · have := dartRuleOutflow_eq_zero_of_deg_ge_9 H fuel d hgt8; omega
    · have h_cases : Hypermap.nodeDegree H d fuel = 5 ∨ Hypermap.nodeDegree H d fuel = 6 ∨
          Hypermap.nodeDegree H d fuel = 7 ∨ Hypermap.nodeDegree H d fuel = 8 := by omega
      rcases h_cases with h5 | h6 | h7 | h8
      · have := dartRuleOutflow_le_6_of_deg_5 H fuel d h5; omega
      · have := dartRuleOutflow_le_6_of_deg_6 H fuel d h6; omega
      · exact dartRuleOutflow_le_7_of_deg_7_of_target_deg_ge_8 H fuel d h7 h_ed
      · have := dartRuleOutflow_le_4_of_deg_8_of_target_deg_ge_8 H fuel d h8 h_ed; omega

/-- Strengthened Per-Dart Inflow Bound into Degree `≥ 8` from Non-Degree-7 Sources:
    if `8 ≤ nodeDegree H (H.edge.f d) fuel` and `nodeDegree H d fuel ≠ 7`, then `dartRuleOutflow H fuel d ≤ 6`. -/
theorem dartRuleOutflow_le_6_of_target_deg_ge_8_of_deg_ne_7 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_ed : 8 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel)
    (h_ne7 : Hypermap.nodeDegree H d fuel ≠ 7) :
    dartRuleOutflow H fuel d ≤ 6 := by
  rcases Nat.lt_or_ge (Hypermap.nodeDegree H d fuel) 5 with hlt5 | hge5
  · have := dartRuleOutflow_eq_zero_of_deg_lt_5 H fuel d hlt5; omega
  · rcases Nat.lt_or_ge 8 (Hypermap.nodeDegree H d fuel) with hgt8 | hle8
    · have := dartRuleOutflow_eq_zero_of_deg_ge_9 H fuel d hgt8; omega
    · have h_cases : Hypermap.nodeDegree H d fuel = 5 ∨ Hypermap.nodeDegree H d fuel = 6 ∨
          Hypermap.nodeDegree H d fuel = 7 ∨ Hypermap.nodeDegree H d fuel = 8 := by omega
      rcases h_cases with h5 | h6 | h7 | h8
      · exact dartRuleOutflow_le_6_of_deg_5 H fuel d h5
      · exact dartRuleOutflow_le_6_of_deg_6 H fuel d h6
      · contradiction
      · have := dartRuleOutflow_le_4_of_deg_8_of_target_deg_ge_8 H fuel d h8 h_ed; omega

/-! ### Checkpoint E.3: Unconditional Global High-Degree `finalCharge ≤ 0` Theorems -/

/-- For any vertex `u` with `20 ≤ nodeDegree H u fuel`, every dart `d` in `u`'s node orbit has
    `netDartShift H fuel d ≤ 7` (with NO hypotheses on neighbor degrees), so
    `initialCharge H u fuel + orbitNetShift H fuel u ≤ 0` (since `60 - 10k + 7k = 60 - 3k ≤ 0` for `k ≥ 20`). -/
theorem initialCharge_add_orbitNetShift_le_zero_of_deg_ge_20 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_deg20 : 20 ≤ Hypermap.nodeDegree H u fuel) :
    initialCharge H u fuel + orbitNetShift H fuel u ≤ 0 := by
  dsimp [initialCharge, orbitNetShift]
  have h_le_c := foldl_add_le_of_le_const (getOrbit H.node fuel u) (fun d => netDartShift H fuel d) 7 (by
    intro d hd
    dsimp [netDartShift]
    have hd_deg : Hypermap.nodeDegree H d fuel = Hypermap.nodeDegree H u fuel :=
      nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hd
    have h_out0 : dartRuleOutflow H fuel d = 0 :=
      dartRuleOutflow_eq_zero_of_deg_ge_9 H fuel d (by omega)
    have h_in7 : dartRuleOutflow H fuel (H.edge.f d) ≤ 7 := by
      apply dartRuleOutflow_le_7_of_target_deg_ge_8 H fuel (H.edge.f d)
      rw [H.edge_involution d]
      omega
    omega)
  dsimp at h_le_c
  have h_len : (getOrbit H.node fuel u).length = Hypermap.nodeDegree H u fuel := rfl
  omega

/-- Unconditional Global High-Degree Discharging Theorem (`deg(u) ≥ 20`):
    for any loopless vertex `u` of degree `≥ 20`, `finalCharge H (rsstChargeShift H fuel) darts u ≤ 0`
    with NO hypotheses on neighbor degrees or incoming darts. -/
theorem finalCharge_le_zero_of_deg_ge_20 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (h_deg20 : 20 ≤ Hypermap.nodeDegree H u fuel) :
    finalCharge H (rsstChargeShift H fuel) darts u ≤ 0 := by
  rw [finalCharge_eq_initialCharge_add_orbitNetShift H darts h_all h_le u h_loopless]
  exact initialCharge_add_orbitNetShift_le_zero_of_deg_ge_20 H darts h_all h_le u h_deg20

/-- For any vertex `u` with `15 ≤ nodeDegree H u fuel` whose neighbors all have degree `≠ 7`,
    every dart `d` in `u`'s node orbit has `netDartShift H fuel d ≤ 6`, so
    `initialCharge H u fuel + orbitNetShift H fuel u ≤ 0` (since `60 - 10k + 6k = 60 - 4k ≤ 0` for `k ≥ 15`). -/
theorem initialCharge_add_orbitNetShift_le_zero_of_deg_ge_15_of_neighbors_ne_7 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_deg15 : 15 ≤ Hypermap.nodeDegree H u fuel)
    (h_ne7 : ∀ d ∈ getOrbit H.node fuel u, Hypermap.nodeDegree H (H.edge.f d) fuel ≠ 7) :
    initialCharge H u fuel + orbitNetShift H fuel u ≤ 0 := by
  dsimp [initialCharge, orbitNetShift]
  have h_le_c := foldl_add_le_of_le_const (getOrbit H.node fuel u) (fun d => netDartShift H fuel d) 6 (by
    intro d hd
    dsimp [netDartShift]
    have hd_deg : Hypermap.nodeDegree H d fuel = Hypermap.nodeDegree H u fuel :=
      nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hd
    have h_out0 : dartRuleOutflow H fuel d = 0 :=
      dartRuleOutflow_eq_zero_of_deg_ge_9 H fuel d (by omega)
    have h_in6 : dartRuleOutflow H fuel (H.edge.f d) ≤ 6 := by
      apply dartRuleOutflow_le_6_of_target_deg_ge_8_of_deg_ne_7 H fuel (H.edge.f d)
      · rw [H.edge_involution d]; omega
      · exact h_ne7 d hd
    omega)
  dsimp at h_le_c
  have h_len : (getOrbit H.node fuel u).length = Hypermap.nodeDegree H u fuel := rfl
  omega

/-- Global High-Degree Discharging Theorem for Non-Degree-7 Neighborhoods (`deg(u) ≥ 15`):
    for any loopless vertex `u` of degree `≥ 15` with no degree-7 neighbors,
    `finalCharge H (rsstChargeShift H fuel) darts u ≤ 0`. -/
theorem finalCharge_le_zero_of_deg_ge_15_of_neighbors_ne_7 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (h_deg15 : 15 ≤ Hypermap.nodeDegree H u fuel)
    (h_ne7 : ∀ d ∈ getOrbit H.node fuel u, Hypermap.nodeDegree H (H.edge.f d) fuel ≠ 7) :
    finalCharge H (rsstChargeShift H fuel) darts u ≤ 0 := by
  rw [finalCharge_eq_initialCharge_add_orbitNetShift H darts h_all h_le u h_loopless]
  exact initialCharge_add_orbitNetShift_le_zero_of_deg_ge_15_of_neighbors_ne_7 H darts h_all h_le u h_deg15 h_ne7

/-- Primal–Dual Unconditional High-Degree Discharging Theorem on `H.dual`:
    on any bridgeless hypermap `H`, any dual vertex (primal face) `u` of degree `≥ 20` satisfies
    `finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0`. -/
theorem dual_finalCharge_le_zero_of_deg_ge_20_of_isBridgeless (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b fuel : Nat} (h_le_b : darts.length ≤ fuel_b) (h_le : darts.length ≤ fuel)
    (h_bridge : Hypermap.isBridgeless H darts fuel_b) (u : H.Dart)
    (h_deg20 : 20 ≤ Hypermap.nodeDegree H.dual u fuel) :
    finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0 := by
  have h_loopless : ∀ d ∈ getOrbit H.dual.node fuel u, Hypermap.sameVertex H.dual (H.dual.edge.f d) u fuel = false :=
    dual_loopless_orbit_of_isBridgeless H darts h_all h_le_b h_le h_bridge u
  exact finalCharge_le_zero_of_deg_ge_20 H.dual darts h_all h_le u h_loopless h_deg20

/-!
### Stage F.1: Flanking-Spoke Rule Coordinate Identities (`ruleVertexDart` at `2` and `3`)
-/

/-- Exact evaluation of `ruleVertexDart H inv d 2`: steps around `1 = H.edge.f d` in `ruleRot H inv` direction. -/
theorem ruleVertexDart_two (H : Hypermap) (inv : Bool) (d : H.Dart) :
    ruleVertexDart H inv d 2 = H.edge.f (ruleRot H inv (H.edge.f d)) := rfl

/-- Exact evaluation of `ruleVertexDart H inv d 3`: steps around `1 = H.edge.f d` in `ruleRotInv H inv` direction. -/
theorem ruleVertexDart_three (H : Hypermap) (inv : Bool) (d : H.Dart) :
    ruleVertexDart H inv d 3 = H.edge.f (ruleRotInv H inv (H.edge.f d)) := rfl

theorem ruleVertexDart_false_two (H : Hypermap) (d : H.Dart) :
    ruleVertexDart H false d 2 = H.edge.f (H.node.f (H.edge.f d)) := rfl

theorem ruleVertexDart_false_three (H : Hypermap) (d : H.Dart) :
    ruleVertexDart H false d 3 = H.edge.f (H.node.inv (H.edge.f d)) := rfl

theorem ruleVertexDart_true_two (H : Hypermap) (d : H.Dart) :
    ruleVertexDart H true d 2 = H.edge.f (H.node.inv (H.edge.f d)) := rfl

theorem ruleVertexDart_true_three (H : Hypermap) (d : H.Dart) :
    ruleVertexDart H true d 3 = H.edge.f (H.node.f (H.edge.f d)) := rfl

/-- General flanking-spoke identity at coordinate `2` for incoming dart `H.edge.f d`. -/
theorem ruleVertexDart_edge_two (H : Hypermap) (inv : Bool) (d : H.Dart) :
    ruleVertexDart H inv (H.edge.f d) 2 = H.edge.f (ruleRot H inv d) := by
  dsimp [ruleVertexDart]
  rw [H.edge_involution d]

/-- General flanking-spoke identity at coordinate `3` for incoming dart `H.edge.f d`. -/
theorem ruleVertexDart_edge_three (H : Hypermap) (inv : Bool) (d : H.Dart) :
    ruleVertexDart H inv (H.edge.f d) 3 = H.edge.f (ruleRotInv H inv d) := by
  dsimp [ruleVertexDart]
  rw [H.edge_involution d]

/-- Flanking-spoke identity (next spoke `H.node.f d`):
    in orientation `inv = false`, coordinate `2` of the incoming dart `H.edge.f d` is `H.edge.f (H.node.f d)`. -/
theorem ruleVertexDart_false_edge_two (H : Hypermap) (d : H.Dart) :
    ruleVertexDart H false (H.edge.f d) 2 = H.edge.f (H.node.f d) :=
  ruleVertexDart_edge_two H false d

/-- Flanking-spoke identity (previous spoke `H.node.inv d`):
    in orientation `inv = false`, coordinate `3` of the incoming dart `H.edge.f d` is `H.edge.f (H.node.inv d)`. -/
theorem ruleVertexDart_false_edge_three (H : Hypermap) (d : H.Dart) :
    ruleVertexDart H false (H.edge.f d) 3 = H.edge.f (H.node.inv d) :=
  ruleVertexDart_edge_three H false d

/-- Reflected flanking-spoke identity (previous spoke `H.node.inv d`):
    in orientation `inv = true`, coordinate `2` of the incoming dart `H.edge.f d` is `H.edge.f (H.node.inv d)`. -/
theorem ruleVertexDart_true_edge_two (H : Hypermap) (d : H.Dart) :
    ruleVertexDart H true (H.edge.f d) 2 = H.edge.f (H.node.inv d) :=
  ruleVertexDart_edge_two H true d

/-- Reflected flanking-spoke identity (next spoke `H.node.f d`):
    in orientation `inv = true`, coordinate `3` of the incoming dart `H.edge.f d` is `H.edge.f (H.node.f d)`. -/
theorem ruleVertexDart_true_edge_three (H : Hypermap) (d : H.Dart) :
    ruleVertexDart H true (H.edge.f d) 3 = H.edge.f (H.node.f d) :=
  ruleVertexDart_edge_three H true d

/-!
### Stage F.2: Flanking-Degree Half-Outflow Bounds & Per-Spoke Inflow Bounds
-/

/-- If `degs 0 < 5`, no rule in `theRules` matches `degs`, so `orientOutflowDegs inv degs = 0`. -/
theorem orientOutflowDegs_eq_zero_of_deg_lt_5 (inv : Bool) (degs : Nat → Nat)
    (h_lt : degs 0 < 5) :
    orientOutflowDegs inv degs = 0 := by
  dsimp [orientOutflowDegs]
  apply foldl_add_eq_zero
  intro r hr
  have hb0 := (theRules_b0_bounds r hr).1
  have h_false : matchesRawRuleDegs degs r = false := by
    dsimp [matchesRawRuleDegs]
    rw [@degMatchesBound_eq_false_of_lt (degs 0) r.b0 (by omega) (by omega)]
    rfl
  rw [h_false]; simp

/-- If `9 ≤ degs 0`, no rule in `theRules` matches `degs`, so `orientOutflowDegs inv degs = 0`. -/
theorem orientOutflowDegs_eq_zero_of_deg_ge_9 (inv : Bool) (degs : Nat → Nat)
    (h_ge : 9 ≤ degs 0) :
    orientOutflowDegs inv degs = 0 := by
  dsimp [orientOutflowDegs]
  apply foldl_add_eq_zero
  intro r hr
  have hb0 := (theRules_b0_bounds r hr).2.2
  have h_false : matchesRawRuleDegs degs r = false := by
    dsimp [matchesRawRuleDegs]
    rw [@degMatchesBound_eq_false_of_gt (degs 0) r.b0 hb0 (by omega)]
    rfl
  rw [h_false]; simp

/-- Universal inverted (`inv = true`) half-outflow bound into target degree `≥ 8`:
    for any source degree `degs 0`, `8 ≤ degs 1 → orientOutflowDegs true degs ≤ 3`. -/
theorem orientOutflowDegs_true_le_3_of_target_deg_ge_8 (degs : Nat → Nat)
    (hb1 : 8 ≤ degs 1) :
    orientOutflowDegs true degs ≤ 3 := by
  rcases Nat.lt_or_ge (degs 0) 5 with hlt5 | hge5
  · have := orientOutflowDegs_eq_zero_of_deg_lt_5 true degs hlt5; omega
  · rcases Nat.lt_or_ge 8 (degs 0) with hgt8 | hle8
    · have := orientOutflowDegs_eq_zero_of_deg_ge_9 true degs hgt8; omega
    · have h_cases : degs 0 = 5 ∨ degs 0 = 6 ∨ degs 0 = 7 ∨ degs 0 = 8 := by omega
      rcases h_cases with h5 | h6 | h7 | h8
      · exact orientOutflowDegs_le_3_of_deg_5 true degs h5
      · exact orientOutflowDegs_le_3_of_deg_6 true degs h6
      · exact orientOutflowDegs_true_le_3_of_deg_7_of_target_deg_ge_8 degs h7 hb1
      · have := orientOutflowDegs_le_2_of_deg_8_of_target_deg_ge_8 true degs h8 hb1; omega

/-- When `degs 0 = 7`, `8 ≤ degs 1`, and `6 ≤ degs 2`, rule `r21` (`(2, (5, 5))`) cannot match,
    so `orientOutflowDegs inv degs ≤ 3` in both orientations. -/
theorem orientOutflowDegs_le_3_of_deg_7_of_target_deg_ge_8_of_deg2_ge_6 (inv : Bool) (degs : Nat → Nat)
    (hb0 : degs 0 = 7) (hb1 : 8 ≤ degs 1) (hb2 : 6 ≤ degs 2) :
    orientOutflowDegs inv degs ≤ 3 := by
  rw [orientOutflowDegs_eq_filter_active inv degs 7 8 hb0 hb1]
  have h_filt : theRules.filter (ruleActiveFor 7 8) =
    [r17, r19, r21, r22, r24, r26, r27, r29, r31, r33, r35, r39, r41, r47, r51] := rfl
  rw [h_filt]
  dsimp only [List.foldl]
  have hc1 := deg7_b1_ge_8_clique1_le_1 inv degs
  have hc2 := conflict_pair_at inv degs r19 r51 3 5 6 7 7 (by decide) (by decide) (by decide) (by decide)
  have hc3 := deg7_b1_ge_8_clique3_le_1 inv degs
  have h21 : matchesRawRuleDegs degs r21 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r21 2 5 5 (by decide) (by decide) (by omega)
  rw [h21]; simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- Universal half-outflow bound when `8 ≤ degs 1` and `6 ≤ degs 2`:
    for ANY source degree `degs 0`, `orientOutflowDegs inv degs ≤ 3`. -/
theorem orientOutflowDegs_le_3_of_target_deg_ge_8_of_deg2_ge_6 (inv : Bool) (degs : Nat → Nat)
    (hb1 : 8 ≤ degs 1) (hb2 : 6 ≤ degs 2) :
    orientOutflowDegs inv degs ≤ 3 := by
  rcases Nat.lt_or_ge (degs 0) 5 with hlt5 | hge5
  · have := orientOutflowDegs_eq_zero_of_deg_lt_5 inv degs hlt5; omega
  · rcases Nat.lt_or_ge 8 (degs 0) with hgt8 | hle8
    · have := orientOutflowDegs_eq_zero_of_deg_ge_9 inv degs hgt8; omega
    · have h_cases : degs 0 = 5 ∨ degs 0 = 6 ∨ degs 0 = 7 ∨ degs 0 = 8 := by omega
      rcases h_cases with h5 | h6 | h7 | h8
      · exact orientOutflowDegs_le_3_of_deg_5 inv degs h5
      · exact orientOutflowDegs_le_3_of_deg_6 inv degs h6
      · exact orientOutflowDegs_le_3_of_deg_7_of_target_deg_ge_8_of_deg2_ge_6 inv degs h7 hb1 hb2
      · have := orientOutflowDegs_le_2_of_deg_8_of_target_deg_ge_8 inv degs h8 hb1; omega

/-- Universal half-outflow bound when `8 ≤ degs 1` and `6 ≤ degs 3`:
    for ANY source degree `degs 0`, `orientOutflowDegs inv degs ≤ 2`. -/
theorem orientOutflowDegs_le_2_of_target_deg_ge_8_of_deg3_ge_6 (inv : Bool) (degs : Nat → Nat)
    (hb1 : 8 ≤ degs 1) (hb3 : 6 ≤ degs 3) :
    orientOutflowDegs inv degs ≤ 2 := by
  rcases Nat.lt_or_ge (degs 0) 5 with hlt5 | hge5
  · have := orientOutflowDegs_eq_zero_of_deg_lt_5 inv degs hlt5; omega
  · rcases Nat.lt_or_ge 8 (degs 0) with hgt8 | hle8
    · have := orientOutflowDegs_eq_zero_of_deg_ge_9 inv degs hgt8; omega
    · have h_cases : degs 0 = 5 ∨ degs 0 = 6 ∨ degs 0 = 7 ∨ degs 0 = 8 := by omega
      rcases h_cases with h5 | h6 | h7 | h8
      · rw [orientOutflowDegs_eq_filter_active inv degs 5 8 h5 hb1]
        have h_filt : theRules.filter (ruleActiveFor 5 8) = [r1, r3, r5] := rfl
        rw [h_filt]; dsimp only [List.foldl]
        have h3 : matchesRawRuleDegs degs r3 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r3 3 5 5 (by decide) (by decide) (by omega)
        have h1 : (if (if inv then r1.invert else true) && matchesRawRuleDegs degs r1 then (1 : Int) else 0) ≤ 1 := by split <;> omega
        have h5' : (if (if inv then r5.invert else true) && matchesRawRuleDegs degs r5 then (1 : Int) else 0) ≤ 1 := by split <;> omega
        rw [h3]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
      · rw [orientOutflowDegs_eq_filter_active inv degs 6 8 h6 hb1]
        have h_filt : theRules.filter (ruleActiveFor 6 8) = [r3, r5, r7, r9, r11, r13, r15] := rfl
        rw [h_filt]; dsimp only [List.foldl]
        have h3 : matchesRawRuleDegs degs r3 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r3 3 5 5 (by decide) (by decide) (by omega)
        have h7 : matchesRawRuleDegs degs r7 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r7 3 5 5 (by decide) (by decide) (by omega)
        have h13 : matchesRawRuleDegs degs r13 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r13 3 5 5 (by decide) (by decide) (by omega)
        have hc5_11 := conflict_pair_at inv degs r5 r11 5 5 5 6 6 (by decide) (by decide) (by decide) (by decide)
        have hc9_15 := conflict_pair_at inv degs r9 r15 9 5 5 6 6 (by decide) (by decide) (by decide) (by decide)
        rw [h3, h7, h13]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
      · rw [orientOutflowDegs_eq_filter_active inv degs 7 8 h7 hb1]
        have h_filt : theRules.filter (ruleActiveFor 7 8) =
          [r17, r19, r21, r22, r24, r26, r27, r29, r31, r33, r35, r39, r41, r47, r51] := rfl
        rw [h_filt]; dsimp only [List.foldl]
        have hc1 := deg7_b1_ge_8_clique1_le_1 inv degs
        have hc2 := conflict_pair_at inv degs r19 r51 3 5 6 7 7 (by decide) (by decide) (by decide) (by decide)
        have h21 : matchesRawRuleDegs degs r21 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r21 3 5 5 (by decide) (by decide) (by omega)
        have h26 : matchesRawRuleDegs degs r26 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r26 3 5 5 (by decide) (by decide) (by omega)
        have h27 : matchesRawRuleDegs degs r27 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r27 3 5 5 (by decide) (by decide) (by omega)
        have h29 : matchesRawRuleDegs degs r29 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r29 3 5 5 (by decide) (by decide) (by omega)
        have h33 : matchesRawRuleDegs degs r33 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r33 3 5 5 (by decide) (by decide) (by omega)
        have h35 : matchesRawRuleDegs degs r35 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r35 3 5 5 (by decide) (by decide) (by omega)
        rw [h21, h26, h27, h29, h33, h35]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
      · exact orientOutflowDegs_le_2_of_deg_8_of_target_deg_ge_8 inv degs h8 hb1

/-- Universal half-outflow bound when `8 ≤ degs 1` and `7 ≤ degs 3`:
    for ANY source degree `degs 0`, `orientOutflowDegs inv degs ≤ 1`. -/
theorem orientOutflowDegs_le_1_of_target_deg_ge_8_of_deg3_ge_7 (inv : Bool) (degs : Nat → Nat)
    (hb1 : 8 ≤ degs 1) (hb3 : 7 ≤ degs 3) :
    orientOutflowDegs inv degs ≤ 1 := by
  rcases Nat.lt_or_ge (degs 0) 5 with hlt5 | hge5
  · have := orientOutflowDegs_eq_zero_of_deg_lt_5 inv degs hlt5; omega
  · rcases Nat.lt_or_ge 8 (degs 0) with hgt8 | hle8
    · have := orientOutflowDegs_eq_zero_of_deg_ge_9 inv degs hgt8; omega
    · have h_cases : degs 0 = 5 ∨ degs 0 = 6 ∨ degs 0 = 7 ∨ degs 0 = 8 := by omega
      rcases h_cases with h5 | h6 | h7 | h8
      · rw [orientOutflowDegs_eq_filter_active inv degs 5 8 h5 hb1]
        have h_filt : theRules.filter (ruleActiveFor 5 8) = [r1, r3, r5] := rfl
        rw [h_filt]; dsimp only [List.foldl]
        have h3 : matchesRawRuleDegs degs r3 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r3 3 5 5 (by decide) (by decide) (by omega)
        have h5' : matchesRawRuleDegs degs r5 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r5 3 5 6 (by decide) (by decide) (by omega)
        have h1 : (if (if inv then r1.invert else true) && matchesRawRuleDegs degs r1 then (1 : Int) else 0) ≤ 1 := by split <;> omega
        rw [h3, h5']; simp only [Bool.and_false, if_false_eq_true_zero]; omega
      · rw [orientOutflowDegs_eq_filter_active inv degs 6 8 h6 hb1]
        have h_filt : theRules.filter (ruleActiveFor 6 8) = [r3, r5, r7, r9, r11, r13, r15] := rfl
        rw [h_filt]; dsimp only [List.foldl]
        have h3 : matchesRawRuleDegs degs r3 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r3 3 5 5 (by decide) (by decide) (by omega)
        have h5 : matchesRawRuleDegs degs r5 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r5 3 5 6 (by decide) (by decide) (by omega)
        have h7 : matchesRawRuleDegs degs r7 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r7 3 5 5 (by decide) (by decide) (by omega)
        have h9 : matchesRawRuleDegs degs r9 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r9 3 6 6 (by decide) (by decide) (by omega)
        have h11 : matchesRawRuleDegs degs r11 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r11 3 6 6 (by decide) (by decide) (by omega)
        have h13 : matchesRawRuleDegs degs r13 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r13 3 5 5 (by decide) (by decide) (by omega)
        have h15 : matchesRawRuleDegs degs r15 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r15 3 6 6 (by decide) (by decide) (by omega)
        rw [h3, h5, h7, h9, h11, h13, h15]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
      · rw [orientOutflowDegs_eq_filter_active inv degs 7 8 h7 hb1]
        have h_filt : theRules.filter (ruleActiveFor 7 8) =
          [r17, r19, r21, r22, r24, r26, r27, r29, r31, r33, r35, r39, r41, r47, r51] := rfl
        rw [h_filt]; dsimp only [List.foldl]
        have h17 : matchesRawRuleDegs degs r17 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r17 3 5 6 (by decide) (by decide) (by omega)
        have h19 : matchesRawRuleDegs degs r19 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r19 3 5 6 (by decide) (by decide) (by omega)
        have h21 : matchesRawRuleDegs degs r21 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r21 3 5 5 (by decide) (by decide) (by omega)
        have h22 : matchesRawRuleDegs degs r22 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r22 3 5 5 (by decide) (by decide) (by omega)
        have h24 : matchesRawRuleDegs degs r24 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r24 3 5 5 (by decide) (by decide) (by omega)
        have h26 : matchesRawRuleDegs degs r26 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r26 3 5 5 (by decide) (by decide) (by omega)
        have h27 : matchesRawRuleDegs degs r27 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r27 3 5 5 (by decide) (by decide) (by omega)
        have h29 : matchesRawRuleDegs degs r29 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r29 3 5 5 (by decide) (by decide) (by omega)
        have h31 : matchesRawRuleDegs degs r31 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r31 3 5 5 (by decide) (by decide) (by omega)
        have h33 : matchesRawRuleDegs degs r33 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r33 3 5 5 (by decide) (by decide) (by omega)
        have h35 : matchesRawRuleDegs degs r35 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r35 3 5 5 (by decide) (by decide) (by omega)
        have h39 : matchesRawRuleDegs degs r39 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r39 3 5 5 (by decide) (by decide) (by omega)
        have h41 : matchesRawRuleDegs degs r41 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r41 3 6 6 (by decide) (by decide) (by omega)
        have hc47_51 := conflict_pair_at inv degs r47 r51 9 5 5 6 6 (by decide) (by decide) (by decide) (by decide)
        rw [h17, h19, h21, h22, h24, h26, h27, h29, h31, h33, h35, h39, h41]
        simp only [Bool.and_false, if_false_eq_true_zero]; omega
      · rw [orientOutflowDegs_eq_filter_active inv degs 8 8 h8 hb1]
        have h_filt : theRules.filter (ruleActiveFor 8 8) = [r57, r59, r61, r63, r64] := rfl
        rw [h_filt]; dsimp only [List.foldl]
        have h57 : matchesRawRuleDegs degs r57 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r57 3 5 5 (by decide) (by decide) (by omega)
        have h59 : matchesRawRuleDegs degs r59 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r59 3 5 5 (by decide) (by decide) (by omega)
        have h61 : matchesRawRuleDegs degs r61 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r61 3 5 5 (by decide) (by decide) (by omega)
        have h63 : matchesRawRuleDegs degs r63 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r63 3 5 5 (by decide) (by decide) (by omega)
        have h64 : matchesRawRuleDegs degs r64 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r64 3 5 5 (by decide) (by decide) (by omega)
        rw [h57, h59, h61, h63, h64]; simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- Half-outflow bound from source degree `≥ 7` into target degree `≥ 8` when `7 ≤ degs 2`:
    `orientOutflowDegs inv degs ≤ 2`. -/
theorem orientOutflowDegs_le_2_of_deg_ge_7_of_target_deg_ge_8_of_deg2_ge_7 (inv : Bool) (degs : Nat → Nat)
    (hb0 : 7 ≤ degs 0) (hb1 : 8 ≤ degs 1) (hb2 : 7 ≤ degs 2) :
    orientOutflowDegs inv degs ≤ 2 := by
  rcases Nat.lt_or_ge 8 (degs 0) with hgt8 | hle8
  · have := orientOutflowDegs_eq_zero_of_deg_ge_9 inv degs hgt8; omega
  · have h_cases : degs 0 = 7 ∨ degs 0 = 8 := by omega
    rcases h_cases with h7 | h8
    · rw [orientOutflowDegs_eq_filter_active inv degs 7 8 h7 hb1]
      have h_filt : theRules.filter (ruleActiveFor 7 8) =
        [r17, r19, r21, r22, r24, r26, r27, r29, r31, r33, r35, r39, r41, r47, r51] := rfl
      rw [h_filt]; dsimp only [List.foldl]
      have hc1 := deg7_b1_ge_8_clique1_le_1 inv degs
      have hc2 := conflict_pair_at inv degs r19 r51 3 5 6 7 7 (by decide) (by decide) (by decide) (by decide)
      have h21 : matchesRawRuleDegs degs r21 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r21 2 5 5 (by decide) (by decide) (by omega)
      have h26 : matchesRawRuleDegs degs r26 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r26 2 5 5 (by decide) (by decide) (by omega)
      have h27 : matchesRawRuleDegs degs r27 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r27 2 5 5 (by decide) (by decide) (by omega)
      have h29 : matchesRawRuleDegs degs r29 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r29 2 6 6 (by decide) (by decide) (by omega)
      have h33 : matchesRawRuleDegs degs r33 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r33 2 6 6 (by decide) (by decide) (by omega)
      have h35 : matchesRawRuleDegs degs r35 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r35 2 6 6 (by decide) (by decide) (by omega)
      rw [h21, h26, h27, h29, h33, h35]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
    · exact orientOutflowDegs_le_2_of_deg_8_of_target_deg_ge_8 inv degs h8 hb1

/-- Per-spoke incoming outflow bound (`≤ 6`) into a vertex `d` of degree `≥ 8`
    when the next spoke's neighbor `H.edge.f (H.node.f d)` has degree `≥ 6`. -/
theorem dartRuleOutflow_le_6_of_target_deg_ge_8_of_next_spoke_ge_6 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_d8 : 8 ≤ Hypermap.nodeDegree H d fuel)
    (h_next6 : 6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel) :
    dartRuleOutflow H fuel (H.edge.f d) ≤ 6 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have hf := orientOutflowDegs_le_3_of_target_deg_ge_8_of_deg2_ge_6 false
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
    (by simpa [H.edge_involution d] using h_d8)
    (by simpa [ruleVertexDart_false_edge_two] using h_next6)
  have ht := orientOutflowDegs_true_le_3_of_target_deg_ge_8
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
    (by simpa [H.edge_involution d] using h_d8)
  omega

/-- Per-spoke incoming outflow bound (`≤ 5`) into a vertex `d` of degree `≥ 8`
    when both flanking spokes' neighbors `H.edge.f (H.node.f d)` and `H.edge.f (H.node.inv d)` have degree `≥ 6`. -/
theorem dartRuleOutflow_le_5_of_target_deg_ge_8_of_flanking_spokes_ge_6 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_d8 : 8 ≤ Hypermap.nodeDegree H d fuel)
    (h_next6 : 6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel)
    (h_prev6 : 6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel) :
    dartRuleOutflow H fuel (H.edge.f d) ≤ 5 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have hf := orientOutflowDegs_le_2_of_target_deg_ge_8_of_deg3_ge_6 false
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
    (by simpa [H.edge_involution d] using h_d8)
    (by simpa [ruleVertexDart_false_edge_three] using h_prev6)
  have ht := orientOutflowDegs_le_2_of_target_deg_ge_8_of_deg3_ge_6 true
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
    (by simpa [H.edge_involution d] using h_d8)
    (by simpa [ruleVertexDart_true_edge_three] using h_next6)
  omega

/-- Per-spoke incoming outflow bound (`≤ 4`) into a vertex `d` of degree `≥ 8`
    when the next spoke's neighbor has degree `≥ 6` and the previous spoke's neighbor has degree `≥ 7`. -/
theorem dartRuleOutflow_le_4_of_target_deg_ge_8_of_next_spoke_ge_6_of_prev_spoke_ge_7 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_d8 : 8 ≤ Hypermap.nodeDegree H d fuel)
    (h_next6 : 6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel)
    (h_prev7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel) :
    dartRuleOutflow H fuel (H.edge.f d) ≤ 4 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have hf := orientOutflowDegs_le_1_of_target_deg_ge_8_of_deg3_ge_7 false
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
    (by simpa [H.edge_involution d] using h_d8)
    (by simpa [ruleVertexDart_false_edge_three] using h_prev7)
  have ht := orientOutflowDegs_le_2_of_target_deg_ge_8_of_deg3_ge_6 true
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
    (by simpa [H.edge_involution d] using h_d8)
    (by simpa [ruleVertexDart_true_edge_three] using h_next6)
  omega

/-- Per-spoke incoming outflow bound (`≤ 3`) into a vertex `d` of degree `≥ 8`
    when the spoke's neighbor and both flanking spokes' neighbors all have degree `≥ 7`. -/
theorem dartRuleOutflow_le_3_of_deg_ge_7_of_target_deg_ge_8_of_flanking_spokes_ge_7 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_d8 : 8 ≤ Hypermap.nodeDegree H d fuel)
    (_h_curr7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel)
    (h_next7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel)
    (h_prev7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel) :
    dartRuleOutflow H fuel (H.edge.f d) ≤ 3 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have hf := orientOutflowDegs_le_1_of_target_deg_ge_8_of_deg3_ge_7 false
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
    (by simpa [H.edge_involution d] using h_d8)
    (by simpa [ruleVertexDart_false_edge_three] using h_prev7)
  have ht := orientOutflowDegs_le_1_of_target_deg_ge_8_of_deg3_ge_7 true
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
    (by simpa [H.edge_involution d] using h_d8)
    (by simpa [ruleVertexDart_true_edge_three] using h_next7)
  omega

/-!
### Stage F.3: Neighborhood-Driven Global High-Degree `finalCharge ≤ 0` Theorems (Primal & Dual)
-/

/-- For any vertex `u` with `12 ≤ nodeDegree H u fuel` whose neighbors all have degree `≥ 6`,
    every spoke `d ∈ getOrbit H.node fuel u` has flanking neighbors `H.node.f d` and `H.node.inv d`
    also of degree `≥ 6`, so `netDartShift H fuel d ≤ 5` and
    `initialCharge H u fuel + orbitNetShift H fuel u ≤ 0` (since `60 - 10k + 5k = 60 - 5k ≤ 0` for `k ≥ 12`). -/
theorem initialCharge_add_orbitNetShift_le_zero_of_deg_ge_12_of_neighbors_deg_ge_6 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_deg12 : 12 ≤ Hypermap.nodeDegree H u fuel)
    (h_nb6 : ∀ d ∈ getOrbit H.node fuel u, 6 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    initialCharge H u fuel + orbitNetShift H fuel u ≤ 0 := by
  dsimp [initialCharge, orbitNetShift]
  have h_le_c := foldl_add_le_of_le_const (getOrbit H.node fuel u) (fun d => netDartShift H fuel d) 5 (by
    intro d hd
    dsimp [netDartShift]
    have hd_deg : Hypermap.nodeDegree H d fuel = Hypermap.nodeDegree H u fuel :=
      nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hd
    have h_out0 : dartRuleOutflow H fuel d = 0 :=
      dartRuleOutflow_eq_zero_of_deg_ge_9 H fuel d (by omega)
    have hd_next : H.node.f d ∈ getOrbit H.node fuel u :=
      Hypermap.getOrbit_closed_under_f_of_complete H.node darts h_all h_le hd
    have hd_prev : H.node.inv d ∈ getOrbit H.node fuel u :=
      Hypermap.getOrbit_closed_under_inv_of_complete H.node darts h_all h_le hd
    have h_in5 : dartRuleOutflow H fuel (H.edge.f d) ≤ 5 :=
      dartRuleOutflow_le_5_of_target_deg_ge_8_of_flanking_spokes_ge_6 H fuel d
        (by omega) (h_nb6 (H.node.f d) hd_next) (h_nb6 (H.node.inv d) hd_prev)
    omega)
  dsimp at h_le_c
  have h_len : (getOrbit H.node fuel u).length = Hypermap.nodeDegree H u fuel := rfl
  omega

/-- Global High-Degree Discharging Theorem for Degree-`≥ 6` Neighborhoods (`deg(u) ≥ 12`):
    for any loopless vertex `u` of degree `≥ 12` whose neighbors all have degree `≥ 6`,
    `finalCharge H (rsstChargeShift H fuel) darts u ≤ 0` with NO raw `netDartShift` hypothesis. -/
theorem finalCharge_le_zero_of_deg_ge_12_of_neighbors_deg_ge_6 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (h_deg12 : 12 ≤ Hypermap.nodeDegree H u fuel)
    (h_nb6 : ∀ d ∈ getOrbit H.node fuel u, 6 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    finalCharge H (rsstChargeShift H fuel) darts u ≤ 0 := by
  rw [finalCharge_eq_initialCharge_add_orbitNetShift H darts h_all h_le u h_loopless]
  exact initialCharge_add_orbitNetShift_le_zero_of_deg_ge_12_of_neighbors_deg_ge_6 H darts h_all h_le u h_deg12 h_nb6

/-- For any vertex `u` with `9 ≤ nodeDegree H u fuel` whose neighbors all have degree `≥ 7`,
    every spoke `d ∈ getOrbit H.node fuel u` has `netDartShift H fuel d ≤ 3`, so
    `initialCharge H u fuel + orbitNetShift H fuel u ≤ 0` (since `60 - 10k + 3k = 60 - 7k ≤ 0` for `k ≥ 9`). -/
theorem initialCharge_add_orbitNetShift_le_zero_of_deg_ge_9_of_neighbors_deg_ge_7 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_deg9 : 9 ≤ Hypermap.nodeDegree H u fuel)
    (h_nb7 : ∀ d ∈ getOrbit H.node fuel u, 7 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    initialCharge H u fuel + orbitNetShift H fuel u ≤ 0 := by
  dsimp [initialCharge, orbitNetShift]
  have h_le_c := foldl_add_le_of_le_const (getOrbit H.node fuel u) (fun d => netDartShift H fuel d) 3 (by
    intro d hd
    dsimp [netDartShift]
    have hd_deg : Hypermap.nodeDegree H d fuel = Hypermap.nodeDegree H u fuel :=
      nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hd
    have h_out0 : dartRuleOutflow H fuel d = 0 :=
      dartRuleOutflow_eq_zero_of_deg_ge_9 H fuel d (by omega)
    have hd_next : H.node.f d ∈ getOrbit H.node fuel u :=
      Hypermap.getOrbit_closed_under_f_of_complete H.node darts h_all h_le hd
    have hd_prev : H.node.inv d ∈ getOrbit H.node fuel u :=
      Hypermap.getOrbit_closed_under_inv_of_complete H.node darts h_all h_le hd
    have h_in3 : dartRuleOutflow H fuel (H.edge.f d) ≤ 3 :=
      dartRuleOutflow_le_3_of_deg_ge_7_of_target_deg_ge_8_of_flanking_spokes_ge_7 H fuel d
        (by omega) (h_nb7 d hd) (h_nb7 (H.node.f d) hd_next) (h_nb7 (H.node.inv d) hd_prev)
    omega)
  dsimp at h_le_c
  have h_len : (getOrbit H.node fuel u).length = Hypermap.nodeDegree H u fuel := rfl
  omega

/-- Global High-Degree Discharging Theorem for Degree-`≥ 7` Neighborhoods (`deg(u) ≥ 9`):
    for any loopless vertex `u` of degree `≥ 9` whose neighbors all have degree `≥ 7`,
    `finalCharge H (rsstChargeShift H fuel) darts u ≤ 0` with NO raw `netDartShift` hypothesis. -/
theorem finalCharge_le_zero_of_deg_ge_9_of_neighbors_deg_ge_7 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (h_deg9 : 9 ≤ Hypermap.nodeDegree H u fuel)
    (h_nb7 : ∀ d ∈ getOrbit H.node fuel u, 7 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    finalCharge H (rsstChargeShift H fuel) darts u ≤ 0 := by
  rw [finalCharge_eq_initialCharge_add_orbitNetShift H darts h_all h_le u h_loopless]
  exact initialCharge_add_orbitNetShift_le_zero_of_deg_ge_9_of_neighbors_deg_ge_7 H darts h_all h_le u h_deg9 h_nb7

/-- Primal–Dual High-Degree Discharging Theorem on `H.dual` (`deg(u) ≥ 12`, neighbors `≥ 6`):
    on any bridgeless hypermap `H`, any dual vertex `u` of degree `≥ 12` whose dual neighbors
    all have degree `≥ 6` satisfies `finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0`. -/
theorem dual_finalCharge_le_zero_of_deg_ge_12_of_isBridgeless_of_neighbors_deg_ge_6 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b fuel : Nat} (h_le_b : darts.length ≤ fuel_b) (h_le : darts.length ≤ fuel)
    (h_bridge : Hypermap.isBridgeless H darts fuel_b) (u : H.Dart)
    (h_deg12 : 12 ≤ Hypermap.nodeDegree H.dual u fuel)
    (h_nb6 : ∀ d ∈ getOrbit H.dual.node fuel u, 6 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f d) fuel) :
    finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0 := by
  have h_loopless : ∀ d ∈ getOrbit H.dual.node fuel u, Hypermap.sameVertex H.dual (H.dual.edge.f d) u fuel = false :=
    dual_loopless_orbit_of_isBridgeless H darts h_all h_le_b h_le h_bridge u
  exact finalCharge_le_zero_of_deg_ge_12_of_neighbors_deg_ge_6 H.dual darts h_all h_le u h_loopless h_deg12 h_nb6

/-- Primal–Dual High-Degree Discharging Theorem on `H.dual` (`deg(u) ≥ 9`, neighbors `≥ 7`):
    on any bridgeless hypermap `H`, any dual vertex `u` of degree `≥ 9` whose dual neighbors
    all have degree `≥ 7` satisfies `finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0`. -/
theorem dual_finalCharge_le_zero_of_deg_ge_9_of_isBridgeless_of_neighbors_deg_ge_7 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b fuel : Nat} (h_le_b : darts.length ≤ fuel_b) (h_le : darts.length ≤ fuel)
    (h_bridge : Hypermap.isBridgeless H darts fuel_b) (u : H.Dart)
    (h_deg9 : 9 ≤ Hypermap.nodeDegree H.dual u fuel)
    (h_nb7 : ∀ d ∈ getOrbit H.dual.node fuel u, 7 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f d) fuel) :
    finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0 := by
  have h_loopless : ∀ d ∈ getOrbit H.dual.node fuel u, Hypermap.sameVertex H.dual (H.dual.edge.f d) u fuel = false :=
    dual_loopless_orbit_of_isBridgeless H darts h_all h_le_b h_le h_bridge u
  exact finalCharge_le_zero_of_deg_ge_9_of_neighbors_deg_ge_7 H.dual darts h_all h_le u h_loopless h_deg9 h_nb7

/-!
### Stage G.1: Faithful Hub-Neighbor Spoke Identities (`2, 3, 6, 7, 15, 16`) & Orbit Closure under `ruleRot` / `ruleRotInv`
-/

/-- `getOrbit H.node fuel u` is closed under `ruleRot H inv` on a complete dart list. -/
theorem getOrbit_closed_under_ruleRot_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u d : H.Dart}
    (hd : d ∈ getOrbit H.node fuel u) (inv : Bool) :
    ruleRot H inv d ∈ getOrbit H.node fuel u := by
  cases inv
  · exact Hypermap.getOrbit_closed_under_f_of_complete H.node darts h_all h_le hd
  · exact Hypermap.getOrbit_closed_under_inv_of_complete H.node darts h_all h_le hd

/-- `getOrbit H.node fuel u` is closed under `ruleRotInv H inv` on a complete dart list. -/
theorem getOrbit_closed_under_ruleRotInv_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u d : H.Dart}
    (hd : d ∈ getOrbit H.node fuel u) (inv : Bool) :
    ruleRotInv H inv d ∈ getOrbit H.node fuel u := by
  cases inv
  · exact Hypermap.getOrbit_closed_under_inv_of_complete H.node darts h_all h_le hd
  · exact Hypermap.getOrbit_closed_under_f_of_complete H.node darts h_all h_le hd

/-- Exact hub-neighbor spoke identity at coordinate `6` for incoming dart `H.edge.f d`:
    two `ruleRot H inv` steps around hub `d`. -/
theorem ruleVertexDart_edge_six (H : Hypermap) (inv : Bool) (d : H.Dart) :
    ruleVertexDart H inv (H.edge.f d) 6 = H.edge.f (ruleRot H inv (ruleRot H inv d)) := by
  dsimp [ruleVertexDart]
  rw [H.edge_involution d]

/-- Exact hub-neighbor spoke identity at coordinate `7` for incoming dart `H.edge.f d`:
    two `ruleRotInv H inv` steps around hub `d`. -/
theorem ruleVertexDart_edge_seven (H : Hypermap) (inv : Bool) (d : H.Dart) :
    ruleVertexDart H inv (H.edge.f d) 7 = H.edge.f (ruleRotInv H inv (ruleRotInv H inv d)) := by
  dsimp [ruleVertexDart]
  rw [H.edge_involution d]

/-- Exact hub-neighbor spoke identity at coordinate `15` for incoming dart `H.edge.f d`:
    three `ruleRot H inv` steps around hub `d`. -/
theorem ruleVertexDart_edge_fifteen (H : Hypermap) (inv : Bool) (d : H.Dart) :
    ruleVertexDart H inv (H.edge.f d) 15 = H.edge.f (ruleRot H inv (ruleRot H inv (ruleRot H inv d))) := by
  dsimp [ruleVertexDart]
  rw [H.edge_involution d]

/-- Exact hub-neighbor spoke identity at coordinate `16` for incoming dart `H.edge.f d`:
    four `ruleRot H inv` steps around hub `d`. -/
theorem ruleVertexDart_edge_sixteen (H : Hypermap) (inv : Bool) (d : H.Dart) :
    ruleVertexDart H inv (H.edge.f d) 16 =
      H.edge.f (ruleRot H inv (ruleRot H inv (ruleRot H inv (ruleRot H inv d)))) := by
  dsimp [ruleVertexDart]
  rw [H.edge_involution d]

/-!
### Stage G.2: Faithful RSST Hub-Neighbor Outflow Vanishing & Sharp Bounds
-/

private def r37 : RawRule := { num := 37, b0 := (7, 7), b1 := (7, 7), triples := [(2, (6, 12)), (3, (5, 5)), (5, (6, 6)), (7, (5, 5)), (9, (5, 5)), (14, (5, 5))], invert := true }
private def r43 : RawRule := { num := 43, b0 := (7, 7), b1 := (7, 7), triples := [(2, (6, 6)), (3, (6, 12)), (4, (5, 6)), (6, (5, 5)), (12, (5, 5)), (13, (5, 5))], invert := true }
private def r45 : RawRule := { num := 45, b0 := (7, 7), b1 := (7, 7), triples := [(2, (6, 6)), (3, (6, 12)), (4, (5, 5)), (6, (5, 5)), (12, (6, 6)), (13, (5, 5))], invert := true }
private def r49 : RawRule := { num := 49, b0 := (7, 7), b1 := (7, 7), triples := [(2, (5, 5)), (3, (7, 12)), (4, (5, 5)), (5, (6, 6)), (6, (5, 5)), (12, (5, 5)), (13, (6, 6))], invert := true }
private def r53 : RawRule := { num := 53, b0 := (7, 7), b1 := (7, 7), triples := [(2, (6, 6)), (3, (7, 12)), (4, (6, 6)), (5, (5, 5)), (6, (5, 5)), (12, (6, 6)), (13, (5, 5))], invert := true }
private def r55 : RawRule := { num := 55, b0 := (7, 7), b1 := (7, 7), triples := [(2, (6, 6)), (3, (7, 7)), (4, (7, 12)), (5, (5, 6)), (6, (6, 6)), (9, (5, 5)), (15, (5, 5)), (16, (6, 12))], invert := true }
private def r66 : RawRule := { num := 66, b0 := (8, 8), b1 := (7, 7), triples := [(2, (6, 6)), (3, (7, 12)), (4, (5, 5)), (5, (6, 6)), (6, (5, 5)), (12, (5, 5)), (13, (5, 5)), (14, (5, 5))], invert := true }

/-- Faithful RSST Flanking-Spoke Vanishing Theorem:
    every rule in `theRules` with `b0 ≥ 6` (`r3..r66`) requires either `degs 2 ≤ 6` or `degs 3 ≤ 6`.
    Therefore, for ANY degree profile `degs : Nat → Nat`, if `6 ≤ degs 0`, `7 ≤ degs 2`, and `7 ≤ degs 3`,
    then `orientOutflowDegs inv degs = 0` (unconditionally on `degs 1` and all other coordinates!). -/
theorem orientOutflowDegs_eq_zero_of_deg_ge_6_of_deg2_ge_7_of_deg3_ge_7 (inv : Bool) (degs : Nat → Nat)
    (hb0 : 6 ≤ degs 0) (hb2 : 7 ≤ degs 2) (hb3 : 7 ≤ degs 3) :
    orientOutflowDegs inv degs = 0 := by
  rcases Nat.lt_or_ge 8 (degs 0) with hgt8 | hle8
  · exact orientOutflowDegs_eq_zero_of_deg_ge_9 inv degs hgt8
  · have h_cases : degs 0 = 6 ∨ degs 0 = 7 ∨ degs 0 = 8 := by omega
    rcases h_cases with h6 | h7 | h8
    · rw [orientOutflowDegs_eq_filter_active inv degs 6 0 h6 (Nat.zero_le _)]
      have h_filt : theRules.filter (ruleActiveFor 6 0) = [r3, r5, r7, r9, r11, r13, r15] := rfl
      rw [h_filt]; dsimp only [List.foldl]
      have h3 : matchesRawRuleDegs degs r3 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r3 3 5 5 (by decide) (by decide) (by omega)
      have h5 : matchesRawRuleDegs degs r5 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r5 3 5 6 (by decide) (by decide) (by omega)
      have h7' : matchesRawRuleDegs degs r7 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r7 3 5 5 (by decide) (by decide) (by omega)
      have h9 : matchesRawRuleDegs degs r9 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r9 3 6 6 (by decide) (by decide) (by omega)
      have h11 : matchesRawRuleDegs degs r11 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r11 3 6 6 (by decide) (by decide) (by omega)
      have h13 : matchesRawRuleDegs degs r13 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r13 3 5 5 (by decide) (by decide) (by omega)
      have h15 : matchesRawRuleDegs degs r15 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r15 3 6 6 (by decide) (by decide) (by omega)
      rw [h3, h5, h7', h9, h11, h13, h15]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
    · rw [orientOutflowDegs_eq_filter_active inv degs 7 0 h7 (Nat.zero_le _)]
      have h_filt : theRules.filter (ruleActiveFor 7 0) =
        [r17, r19, r21, r22, r24, r26, r27, r29, r31, r33, r35, r37, r39, r41, r43, r45, r47, r49, r51, r53, r55] := rfl
      rw [h_filt]; dsimp only [List.foldl]
      have h17 : matchesRawRuleDegs degs r17 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r17 3 5 6 (by decide) (by decide) (by omega)
      have h19 : matchesRawRuleDegs degs r19 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r19 3 5 6 (by decide) (by decide) (by omega)
      have h21 : matchesRawRuleDegs degs r21 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r21 3 5 5 (by decide) (by decide) (by omega)
      have h22 : matchesRawRuleDegs degs r22 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r22 3 5 5 (by decide) (by decide) (by omega)
      have h24 : matchesRawRuleDegs degs r24 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r24 3 5 5 (by decide) (by decide) (by omega)
      have h26 : matchesRawRuleDegs degs r26 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r26 3 5 5 (by decide) (by decide) (by omega)
      have h27 : matchesRawRuleDegs degs r27 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r27 3 5 5 (by decide) (by decide) (by omega)
      have h29 : matchesRawRuleDegs degs r29 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r29 3 5 5 (by decide) (by decide) (by omega)
      have h31 : matchesRawRuleDegs degs r31 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r31 3 5 5 (by decide) (by decide) (by omega)
      have h33 : matchesRawRuleDegs degs r33 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r33 3 5 5 (by decide) (by decide) (by omega)
      have h35 : matchesRawRuleDegs degs r35 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r35 3 5 5 (by decide) (by decide) (by omega)
      have h37 : matchesRawRuleDegs degs r37 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r37 3 5 5 (by decide) (by decide) (by omega)
      have h39 : matchesRawRuleDegs degs r39 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r39 3 5 5 (by decide) (by decide) (by omega)
      have h41 : matchesRawRuleDegs degs r41 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r41 3 6 6 (by decide) (by decide) (by omega)
      have h43 : matchesRawRuleDegs degs r43 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r43 2 6 6 (by decide) (by decide) (by omega)
      have h45 : matchesRawRuleDegs degs r45 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r45 2 6 6 (by decide) (by decide) (by omega)
      have h47 : matchesRawRuleDegs degs r47 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r47 2 5 5 (by decide) (by decide) (by omega)
      have h49 : matchesRawRuleDegs degs r49 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r49 2 5 5 (by decide) (by decide) (by omega)
      have h51 : matchesRawRuleDegs degs r51 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r51 2 5 5 (by decide) (by decide) (by omega)
      have h53 : matchesRawRuleDegs degs r53 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r53 2 6 6 (by decide) (by decide) (by omega)
      have h55 : matchesRawRuleDegs degs r55 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r55 2 6 6 (by decide) (by decide) (by omega)
      rw [h17, h19, h21, h22, h24, h26, h27, h29, h31, h33, h35, h37, h39, h41, h43, h45, h47, h49, h51, h53, h55]
      simp only [Bool.and_false, if_false_eq_true_zero]; omega
    · rw [orientOutflowDegs_eq_filter_active inv degs 8 0 h8 (Nat.zero_le _)]
      have h_filt : theRules.filter (ruleActiveFor 8 0) = [r57, r59, r61, r63, r64, r66] := rfl
      rw [h_filt]; dsimp only [List.foldl]
      have h57 : matchesRawRuleDegs degs r57 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r57 2 5 5 (by decide) (by decide) (by omega)
      have h59 : matchesRawRuleDegs degs r59 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r59 2 5 5 (by decide) (by decide) (by omega)
      have h61 : matchesRawRuleDegs degs r61 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r61 2 5 5 (by decide) (by decide) (by omega)
      have h63 : matchesRawRuleDegs degs r63 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r63 2 5 5 (by decide) (by decide) (by omega)
      have h64 : matchesRawRuleDegs degs r64 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r64 2 5 5 (by decide) (by decide) (by omega)
      have h66 : matchesRawRuleDegs degs r66 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r66 2 6 6 (by decide) (by decide) (by omega)
      rw [h57, h59, h61, h63, h64, h66]; simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- Exact vanishing of incoming outflow from any neighbor `H.edge.f d` of degree `≥ 6`
    whenever both flanking spokes `H.node.f d` and `H.node.inv d` have neighbors of degree `≥ 7`
    (unconditional on `nodeDegree H d fuel`!). -/
theorem dartRuleOutflow_eq_zero_of_deg_ge_6_of_flanking_spokes_ge_7 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_curr6 : 6 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel)
    (h_next7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel)
    (h_prev7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel) :
    dartRuleOutflow H fuel (H.edge.f d) = 0 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have hf := orientOutflowDegs_eq_zero_of_deg_ge_6_of_deg2_ge_7_of_deg3_ge_7 false
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
    (by simpa using h_curr6)
    (by simpa [ruleVertexDart_false_edge_two] using h_next7)
    (by simpa [ruleVertexDart_false_edge_three] using h_prev7)
  have ht := orientOutflowDegs_eq_zero_of_deg_ge_6_of_deg2_ge_7_of_deg3_ge_7 true
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
    (by simpa using h_curr6)
    (by simpa [ruleVertexDart_true_edge_two] using h_prev7)
    (by simpa [ruleVertexDart_true_edge_three] using h_next7)
  omega

/-- Corollary (`≤ 2`) for backward compatibility when `7 ≤ deg(H.edge.f d)` and flanking spokes have degree `≥ 7`. -/
theorem dartRuleOutflow_le_2_of_deg_ge_7_of_flanking_spokes_ge_7 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_curr7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel)
    (h_next7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel)
    (h_prev7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel) :
    dartRuleOutflow H fuel (H.edge.f d) ≤ 2 := by
  have h0 := dartRuleOutflow_eq_zero_of_deg_ge_6_of_flanking_spokes_ge_7 H fuel d (by omega) h_next7 h_prev7
  omega

/-- Faithful RSST Degree-`≥ 8` Vanishing Theorem:
    among the 6 rules with `b0 = 8`, `r57..r64` require `degs 2 = 5` and `r66` requires `degs 6 = 5`.
    Therefore, for ANY `degs : Nat → Nat`, if `8 ≤ degs 0`, `6 ≤ degs 2`, and `6 ≤ degs 6`,
    then `orientOutflowDegs inv degs = 0`. -/
theorem orientOutflowDegs_eq_zero_of_deg_ge_8_of_deg2_ge_6_of_deg6_ge_6 (inv : Bool) (degs : Nat → Nat)
    (hb0 : 8 ≤ degs 0) (hb2 : 6 ≤ degs 2) (hb6 : 6 ≤ degs 6) :
    orientOutflowDegs inv degs = 0 := by
  rcases Nat.lt_or_ge 8 (degs 0) with hgt8 | hle8
  · exact orientOutflowDegs_eq_zero_of_deg_ge_9 inv degs hgt8
  · have h8 : degs 0 = 8 := by omega
    rw [orientOutflowDegs_eq_filter_active inv degs 8 0 h8 (Nat.zero_le _)]
    have h_filt : theRules.filter (ruleActiveFor 8 0) = [r57, r59, r61, r63, r64, r66] := rfl
    rw [h_filt]; dsimp only [List.foldl]
    have h57 : matchesRawRuleDegs degs r57 = false :=
      not_matchesRawRuleDegs_of_triple_gt degs r57 2 5 5 (by decide) (by decide) (by omega)
    have h59 : matchesRawRuleDegs degs r59 = false :=
      not_matchesRawRuleDegs_of_triple_gt degs r59 2 5 5 (by decide) (by decide) (by omega)
    have h61 : matchesRawRuleDegs degs r61 = false :=
      not_matchesRawRuleDegs_of_triple_gt degs r61 2 5 5 (by decide) (by decide) (by omega)
    have h63 : matchesRawRuleDegs degs r63 = false :=
      not_matchesRawRuleDegs_of_triple_gt degs r63 2 5 5 (by decide) (by decide) (by omega)
    have h64 : matchesRawRuleDegs degs r64 = false :=
      not_matchesRawRuleDegs_of_triple_gt degs r64 2 5 5 (by decide) (by decide) (by omega)
    have h66 : matchesRawRuleDegs degs r66 = false :=
      not_matchesRawRuleDegs_of_triple_gt degs r66 6 5 5 (by decide) (by decide) (by omega)
    rw [h57, h59, h61, h63, h64, h66]; simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- Exact vanishing of incoming outflow from a neighbor `H.edge.f d` of degree `≥ 8`
    whenever the first and second spokes in both directions around `d` have neighbors of degree `≥ 6`. -/
theorem dartRuleOutflow_eq_zero_of_deg_ge_8_of_two_step_spokes_ge_6 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_curr8 : 8 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel)
    (h_f1 : 6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel)
    (h_f2 : 6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f (H.node.f d))) fuel)
    (h_i1 : 6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel)
    (h_i2 : 6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv (H.node.inv d))) fuel) :
    dartRuleOutflow H fuel (H.edge.f d) = 0 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have hf := orientOutflowDegs_eq_zero_of_deg_ge_8_of_deg2_ge_6_of_deg6_ge_6 false
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
    (by simpa using h_curr8)
    (by simpa [ruleVertexDart_false_edge_two] using h_f1)
    (by simpa [ruleVertexDart_edge_six, ruleRot] using h_f2)
  have ht := orientOutflowDegs_eq_zero_of_deg_ge_8_of_deg2_ge_6_of_deg6_ge_6 true
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
    (by simpa using h_curr8)
    (by simpa [ruleVertexDart_true_edge_two] using h_i1)
    (by simpa [ruleVertexDart_edge_six, ruleRot] using h_i2)
  omega

/-- Faithful RSST Hub-Neighbor Half-Outflow Bound (`≤ 2`) when `degs 0, 2, 3, 6, 7, 15 ≥ 6`:
    - Every `b1 = (7, 7)` rule (`r37, r43, r45, r49, r53, r55, r66`) requires at least one of
      coordinates `2, 3, 6, 7, 15` to have degree `5`, so all 7 vanish!
    - For `b0 = 6`: only `{r5, r9, r11}` survive, and `r5 ⊥ r11` at coordinate `5`, giving `≤ 2`.
    - For `b0 = 7`: only `{r17, r19, r41}` survive, and `r17 ⊥ r41` at coordinate `5`, giving `≤ 2`.
    - For `b0 ≥ 8`: `orientOutflowDegs inv degs = 0 ≤ 2`. -/
theorem orientOutflowDegs_le_2_of_deg_ge_6_of_hub_neighbors_ge_6 (inv : Bool) (degs : Nat → Nat)
    (hb0 : 6 ≤ degs 0) (hb2 : 6 ≤ degs 2) (hb3 : 6 ≤ degs 3)
    (hb6 : 6 ≤ degs 6) (hb7 : 6 ≤ degs 7) (hb15 : 6 ≤ degs 15) :
    orientOutflowDegs inv degs ≤ 2 := by
  rcases Nat.lt_or_ge 7 (degs 0) with hge8 | hle7
  · have h0 := orientOutflowDegs_eq_zero_of_deg_ge_8_of_deg2_ge_6_of_deg6_ge_6 inv degs hge8 hb2 hb6
    omega
  · have h_cases : degs 0 = 6 ∨ degs 0 = 7 := by omega
    rcases h_cases with h6 | h7
    · rw [orientOutflowDegs_eq_filter_active inv degs 6 0 h6 (Nat.zero_le _)]
      have h_filt : theRules.filter (ruleActiveFor 6 0) = [r3, r5, r7, r9, r11, r13, r15] := rfl
      rw [h_filt]; dsimp only [List.foldl]
      have h3 : matchesRawRuleDegs degs r3 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r3 3 5 5 (by decide) (by decide) (by omega)
      have h7' : matchesRawRuleDegs degs r7 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r7 3 5 5 (by decide) (by decide) (by omega)
      have h13 : matchesRawRuleDegs degs r13 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r13 3 5 5 (by decide) (by decide) (by omega)
      have h15 : matchesRawRuleDegs degs r15 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r15 7 5 5 (by decide) (by decide) (by omega)
      have hc5_11 := conflict_pair_at inv degs r5 r11 5 5 5 6 6 (by decide) (by decide) (by decide) (by decide)
      have h9 : (if (if inv then r9.invert else true) && matchesRawRuleDegs degs r9 then (1 : Int) else 0) ≤ 1 := by split <;> omega
      rw [h3, h7', h13, h15]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
    · rw [orientOutflowDegs_eq_filter_active inv degs 7 0 h7 (Nat.zero_le _)]
      have h_filt : theRules.filter (ruleActiveFor 7 0) =
        [r17, r19, r21, r22, r24, r26, r27, r29, r31, r33, r35, r37, r39, r41, r43, r45, r47, r49, r51, r53, r55] := rfl
      rw [h_filt]; dsimp only [List.foldl]
      have h21 : matchesRawRuleDegs degs r21 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r21 3 5 5 (by decide) (by decide) (by omega)
      have h22 : matchesRawRuleDegs degs r22 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r22 3 5 5 (by decide) (by decide) (by omega)
      have h24 : matchesRawRuleDegs degs r24 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r24 3 5 5 (by decide) (by decide) (by omega)
      have h26 : matchesRawRuleDegs degs r26 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r26 3 5 5 (by decide) (by decide) (by omega)
      have h27 : matchesRawRuleDegs degs r27 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r27 3 5 5 (by decide) (by decide) (by omega)
      have h29 : matchesRawRuleDegs degs r29 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r29 3 5 5 (by decide) (by decide) (by omega)
      have h31 : matchesRawRuleDegs degs r31 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r31 3 5 5 (by decide) (by decide) (by omega)
      have h33 : matchesRawRuleDegs degs r33 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r33 3 5 5 (by decide) (by decide) (by omega)
      have h35 : matchesRawRuleDegs degs r35 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r35 3 5 5 (by decide) (by decide) (by omega)
      have h37 : matchesRawRuleDegs degs r37 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r37 3 5 5 (by decide) (by decide) (by omega)
      have h39 : matchesRawRuleDegs degs r39 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r39 3 5 5 (by decide) (by decide) (by omega)
      have h43 : matchesRawRuleDegs degs r43 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r43 6 5 5 (by decide) (by decide) (by omega)
      have h45 : matchesRawRuleDegs degs r45 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r45 6 5 5 (by decide) (by decide) (by omega)
      have h47 : matchesRawRuleDegs degs r47 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r47 2 5 5 (by decide) (by decide) (by omega)
      have h49 : matchesRawRuleDegs degs r49 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r49 2 5 5 (by decide) (by decide) (by omega)
      have h51 : matchesRawRuleDegs degs r51 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r51 2 5 5 (by decide) (by decide) (by omega)
      have h53 : matchesRawRuleDegs degs r53 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r53 6 5 5 (by decide) (by decide) (by omega)
      have h55 : matchesRawRuleDegs degs r55 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r55 15 5 5 (by decide) (by decide) (by omega)
      have hc17_41 := conflict_pair_at inv degs r17 r41 5 5 5 6 6 (by decide) (by decide) (by decide) (by decide)
      have h19 : (if (if inv then r19.invert else true) && matchesRawRuleDegs degs r19 then (1 : Int) else 0) ≤ 1 := by split <;> omega
      rw [h21, h22, h24, h26, h27, h29, h31, h33, h35, h37, h39, h43, h45, h47, h49, h51, h53, h55]
      simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- Sharp per-spoke incoming outflow bound (`≤ 4`, unconditional on hub degree `deg(u)`)
    whenever all neighbors of hub `u` have degree `≥ 6`. -/
theorem dartRuleOutflow_le_4_of_mem_getOrbit_of_neighbors_deg_ge_6 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u d : H.Dart}
    (hd : d ∈ getOrbit H.node fuel u)
    (h_nb6 : ∀ d' ∈ getOrbit H.node fuel u, 6 ≤ Hypermap.nodeDegree H (H.edge.f d') fuel) :
    dartRuleOutflow H fuel (H.edge.f d) ≤ 4 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have h_rot : ∀ (inv : Bool) (d' : H.Dart), d' ∈ getOrbit H.node fuel u →
      ruleRot H inv d' ∈ getOrbit H.node fuel u :=
    fun inv d' hd' => getOrbit_closed_under_ruleRot_of_complete H darts h_all h_le hd' inv
  have h_rotInv : ∀ (inv : Bool) (d' : H.Dart), d' ∈ getOrbit H.node fuel u →
      ruleRotInv H inv d' ∈ getOrbit H.node fuel u :=
    fun inv d' hd' => getOrbit_closed_under_ruleRotInv_of_complete H darts h_all h_le hd' inv
  have hf := orientOutflowDegs_le_2_of_deg_ge_6_of_hub_neighbors_ge_6 false
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
    (by simpa [ruleVertexDart] using h_nb6 d hd)
    (by simpa [ruleVertexDart_edge_two] using h_nb6 _ (h_rot false d hd))
    (by simpa [ruleVertexDart_edge_three] using h_nb6 _ (h_rotInv false d hd))
    (by simpa [ruleVertexDart_edge_six] using h_nb6 _ (h_rot false _ (h_rot false d hd)))
    (by simpa [ruleVertexDart_edge_seven] using h_nb6 _ (h_rotInv false _ (h_rotInv false d hd)))
    (by simpa [ruleVertexDart_edge_fifteen] using h_nb6 _ (h_rot false _ (h_rot false _ (h_rot false d hd))))
  have ht := orientOutflowDegs_le_2_of_deg_ge_6_of_hub_neighbors_ge_6 true
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
    (by simpa [ruleVertexDart] using h_nb6 d hd)
    (by simpa [ruleVertexDart_edge_two] using h_nb6 _ (h_rot true d hd))
    (by simpa [ruleVertexDart_edge_three] using h_nb6 _ (h_rotInv true d hd))
    (by simpa [ruleVertexDart_edge_six] using h_nb6 _ (h_rot true _ (h_rot true d hd)))
    (by simpa [ruleVertexDart_edge_seven] using h_nb6 _ (h_rotInv true _ (h_rotInv true d hd)))
    (by simpa [ruleVertexDart_edge_fifteen] using h_nb6 _ (h_rot true _ (h_rot true _ (h_rot true d hd))))
  omega

/-- When `degs 0 = 5` and `5 ≤ degs 1`, Rule 1 fires in both orientations, so `1 ≤ orientOutflowDegs inv degs`. -/
theorem one_le_orientOutflowDegs_of_deg_5_of_target_deg_ge_5 (inv : Bool) (degs : Nat → Nat)
    (hb0 : degs 0 = 5) (hb1 : 5 ≤ degs 1) :
    1 ≤ orientOutflowDegs inv degs := by
  rw [orientOutflowDegs_eq_filter_active inv degs 5 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 5 0) = [r1, r3, r5] := rfl
  rw [h_filt]; dsimp only [List.foldl]
  have hr1 : matchesRawRuleDegs degs r1 = true := by
    dsimp [matchesRawRuleDegs, r1, degMatchesBound]
    rw [hb0, decide_eq_true hb1]
    rfl
  have h_inv : (if inv then r1.invert else true) = true := by cases inv <;> rfl
  have h3 : 0 ≤ (if (if inv then r3.invert else true) && matchesRawRuleDegs degs r3 then (1 : Int) else 0) := by split <;> omega
  have h5 : 0 ≤ (if (if inv then r5.invert else true) && matchesRawRuleDegs degs r5 then (1 : Int) else 0) := by split <;> omega
  rw [hr1, h_inv]; dsimp; omega

/-!
### Stage G.3: Global Discharging Theorems for Degrees `≥ 6` (`neighbors ≥ 7`), Degrees `≥ 6` (`neighbors ≥ 8`), and Degrees `≥ 10` (`neighbors ≥ 6`)
-/

/-- For any vertex `u` with `6 ≤ nodeDegree H u fuel` whose neighbors all have degree `≥ 7`,
    every spoke `d ∈ getOrbit H.node fuel u` has incoming outflow `= 0` and outgoing outflow `≥ 0`,
    so `netDartShift H fuel d ≤ 0` and `initialCharge H u fuel + orbitNetShift H fuel u ≤ 0`. -/
theorem initialCharge_add_orbitNetShift_le_zero_of_deg_ge_6_of_neighbors_deg_ge_7 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_deg6 : 6 ≤ Hypermap.nodeDegree H u fuel)
    (h_nb7 : ∀ d ∈ getOrbit H.node fuel u, 7 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    initialCharge H u fuel + orbitNetShift H fuel u ≤ 0 := by
  dsimp [initialCharge, orbitNetShift]
  have h_le_c := foldl_add_le_of_le_const (getOrbit H.node fuel u) (fun d => netDartShift H fuel d) 0 (by
    intro d hd
    dsimp [netDartShift]
    have h_out_nonneg : 0 ≤ dartRuleOutflow H fuel d := dartRuleOutflow_nonneg H fuel d
    have hd_next : H.node.f d ∈ getOrbit H.node fuel u :=
      Hypermap.getOrbit_closed_under_f_of_complete H.node darts h_all h_le hd
    have hd_prev : H.node.inv d ∈ getOrbit H.node fuel u :=
      Hypermap.getOrbit_closed_under_inv_of_complete H.node darts h_all h_le hd
    have h_curr6 : 6 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel := by
      have := h_nb7 d hd; omega
    have h_in0 : dartRuleOutflow H fuel (H.edge.f d) = 0 :=
      dartRuleOutflow_eq_zero_of_deg_ge_6_of_flanking_spokes_ge_7 H fuel d
        h_curr6 (h_nb7 (H.node.f d) hd_next) (h_nb7 (H.node.inv d) hd_prev)
    omega)
  dsimp at h_le_c
  have h_len : (getOrbit H.node fuel u).length = Hypermap.nodeDegree H u fuel := rfl
  omega

/-- Global Discharging Theorem for ALL Degrees `≥ 6` (Degrees 6, 7, 8, 9, ...) with Degree-`≥ 7` Neighbors:
    for any loopless vertex `u` of degree `≥ 6` whose neighbors all have degree `≥ 7`,
    `finalCharge H (rsstChargeShift H fuel) darts u ≤ 0`. -/
theorem finalCharge_le_zero_of_deg_ge_6_of_neighbors_deg_ge_7 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (h_deg6 : 6 ≤ Hypermap.nodeDegree H u fuel)
    (h_nb7 : ∀ d ∈ getOrbit H.node fuel u, 7 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    finalCharge H (rsstChargeShift H fuel) darts u ≤ 0 := by
  rw [finalCharge_eq_initialCharge_add_orbitNetShift H darts h_all h_le u h_loopless]
  exact initialCharge_add_orbitNetShift_le_zero_of_deg_ge_6_of_neighbors_deg_ge_7 H darts h_all h_le u h_deg6 h_nb7

/-- Corollary for `8 ≤ deg(u)` with `neighbors ≥ 7`. -/
theorem initialCharge_add_orbitNetShift_le_zero_of_deg_ge_8_of_neighbors_deg_ge_7 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_deg8 : 8 ≤ Hypermap.nodeDegree H u fuel)
    (h_nb7 : ∀ d ∈ getOrbit H.node fuel u, 7 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    initialCharge H u fuel + orbitNetShift H fuel u ≤ 0 :=
  initialCharge_add_orbitNetShift_le_zero_of_deg_ge_6_of_neighbors_deg_ge_7 H darts h_all h_le u (by omega) h_nb7

/-- Global Discharging Theorem for Degree `≥ 8` with Degree-`≥ 7` Neighbors. -/
theorem finalCharge_le_zero_of_deg_ge_8_of_neighbors_deg_ge_7 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (h_deg8 : 8 ≤ Hypermap.nodeDegree H u fuel)
    (h_nb7 : ∀ d ∈ getOrbit H.node fuel u, 7 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    finalCharge H (rsstChargeShift H fuel) darts u ≤ 0 :=
  finalCharge_le_zero_of_deg_ge_6_of_neighbors_deg_ge_7 H darts h_all h_le u h_loopless (by omega) h_nb7

/-- For any vertex `u` with `6 ≤ nodeDegree H u fuel` whose neighbors all have degree `≥ 8`,
    `initialCharge H u fuel + orbitNetShift H fuel u ≤ 0`. -/
theorem initialCharge_add_orbitNetShift_le_zero_of_deg_ge_6_of_neighbors_deg_ge_8 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_deg6 : 6 ≤ Hypermap.nodeDegree H u fuel)
    (h_nb8 : ∀ d ∈ getOrbit H.node fuel u, 8 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    initialCharge H u fuel + orbitNetShift H fuel u ≤ 0 :=
  initialCharge_add_orbitNetShift_le_zero_of_deg_ge_6_of_neighbors_deg_ge_7 H darts h_all h_le u h_deg6
    (fun d hd => by have := h_nb8 d hd; omega)

/-- Global Discharging Theorem for Degree `≥ 6` (Including Degree 7!) with Degree-`≥ 8` Neighbors. -/
theorem finalCharge_le_zero_of_deg_ge_6_of_neighbors_deg_ge_8 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (h_deg6 : 6 ≤ Hypermap.nodeDegree H u fuel)
    (h_nb8 : ∀ d ∈ getOrbit H.node fuel u, 8 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    finalCharge H (rsstChargeShift H fuel) darts u ≤ 0 :=
  finalCharge_le_zero_of_deg_ge_6_of_neighbors_deg_ge_7 H darts h_all h_le u h_loopless h_deg6
    (fun d hd => by have := h_nb8 d hd; omega)

/-- For any vertex `u` with `10 ≤ nodeDegree H u fuel` whose neighbors all have degree `≥ 6`,
    every spoke `d ∈ getOrbit H.node fuel u` has incoming outflow `≤ 4` and outgoing outflow `= 0`,
    so `netDartShift H fuel d ≤ 4` and `initialCharge H u fuel + orbitNetShift H fuel u ≤ 0`
    (since `60 - 10k + 4k = 60 - 6k ≤ 0` for `k ≥ 10`). -/
theorem initialCharge_add_orbitNetShift_le_zero_of_deg_ge_10_of_neighbors_deg_ge_6 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_deg10 : 10 ≤ Hypermap.nodeDegree H u fuel)
    (h_nb6 : ∀ d ∈ getOrbit H.node fuel u, 6 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    initialCharge H u fuel + orbitNetShift H fuel u ≤ 0 := by
  dsimp [initialCharge, orbitNetShift]
  have h_le_c := foldl_add_le_of_le_const (getOrbit H.node fuel u) (fun d => netDartShift H fuel d) 4 (by
    intro d hd
    dsimp [netDartShift]
    have hd_deg : Hypermap.nodeDegree H d fuel = Hypermap.nodeDegree H u fuel :=
      nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hd
    have h_out0 : dartRuleOutflow H fuel d = 0 :=
      dartRuleOutflow_eq_zero_of_deg_ge_9 H fuel d (by omega)
    have h_in4 : dartRuleOutflow H fuel (H.edge.f d) ≤ 4 :=
      dartRuleOutflow_le_4_of_mem_getOrbit_of_neighbors_deg_ge_6 H darts h_all h_le hd h_nb6
    omega)
  dsimp at h_le_c
  have h_len : (getOrbit H.node fuel u).length = Hypermap.nodeDegree H u fuel := rfl
  omega

/-- Global Discharging Theorem for Degree `≥ 10` with Degree-`≥ 6` Neighbors:
    for any loopless vertex `u` of degree `≥ 10` whose neighbors all have degree `≥ 6`,
    `finalCharge H (rsstChargeShift H fuel) darts u ≤ 0`. -/
theorem finalCharge_le_zero_of_deg_ge_10_of_neighbors_deg_ge_6 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (h_deg10 : 10 ≤ Hypermap.nodeDegree H u fuel)
    (h_nb6 : ∀ d ∈ getOrbit H.node fuel u, 6 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    finalCharge H (rsstChargeShift H fuel) darts u ≤ 0 := by
  rw [finalCharge_eq_initialCharge_add_orbitNetShift H darts h_all h_le u h_loopless]
  exact initialCharge_add_orbitNetShift_le_zero_of_deg_ge_10_of_neighbors_deg_ge_6 H darts h_all h_le u h_deg10 h_nb6

/-- Primal–Dual Discharging Theorem on `H.dual` (`deg(u) ≥ 6`, neighbors `≥ 7`):
    on any bridgeless hypermap `H`, any dual vertex `u` of degree `≥ 6` whose dual neighbors
    all have degree `≥ 7` satisfies `finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0`. -/
theorem dual_finalCharge_le_zero_of_deg_ge_6_of_isBridgeless_of_neighbors_deg_ge_7 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b fuel : Nat} (h_le_b : darts.length ≤ fuel_b) (h_le : darts.length ≤ fuel)
    (h_bridge : Hypermap.isBridgeless H darts fuel_b) (u : H.Dart)
    (h_deg6 : 6 ≤ Hypermap.nodeDegree H.dual u fuel)
    (h_nb7 : ∀ d ∈ getOrbit H.dual.node fuel u, 7 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f d) fuel) :
    finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0 := by
  have h_loopless : ∀ d ∈ getOrbit H.dual.node fuel u, Hypermap.sameVertex H.dual (H.dual.edge.f d) u fuel = false :=
    dual_loopless_orbit_of_isBridgeless H darts h_all h_le_b h_le h_bridge u
  exact finalCharge_le_zero_of_deg_ge_6_of_neighbors_deg_ge_7 H.dual darts h_all h_le u h_loopless h_deg6 h_nb7

/-- Primal–Dual Discharging Theorem on `H.dual` (`deg(u) ≥ 8`, neighbors `≥ 7`). -/
theorem dual_finalCharge_le_zero_of_deg_ge_8_of_isBridgeless_of_neighbors_deg_ge_7 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b fuel : Nat} (h_le_b : darts.length ≤ fuel_b) (h_le : darts.length ≤ fuel)
    (h_bridge : Hypermap.isBridgeless H darts fuel_b) (u : H.Dart)
    (h_deg8 : 8 ≤ Hypermap.nodeDegree H.dual u fuel)
    (h_nb7 : ∀ d ∈ getOrbit H.dual.node fuel u, 7 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f d) fuel) :
    finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0 :=
  dual_finalCharge_le_zero_of_deg_ge_6_of_isBridgeless_of_neighbors_deg_ge_7 H darts h_all h_le_b h_le h_bridge u
    (by omega) h_nb7

/-- Primal–Dual Discharging Theorem on `H.dual` (`deg(u) ≥ 6`, neighbors `≥ 8`). -/
theorem dual_finalCharge_le_zero_of_deg_ge_6_of_isBridgeless_of_neighbors_deg_ge_8 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b fuel : Nat} (h_le_b : darts.length ≤ fuel_b) (h_le : darts.length ≤ fuel)
    (h_bridge : Hypermap.isBridgeless H darts fuel_b) (u : H.Dart)
    (h_deg6 : 6 ≤ Hypermap.nodeDegree H.dual u fuel)
    (h_nb8 : ∀ d ∈ getOrbit H.dual.node fuel u, 8 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f d) fuel) :
    finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0 :=
  dual_finalCharge_le_zero_of_deg_ge_6_of_isBridgeless_of_neighbors_deg_ge_7 H darts h_all h_le_b h_le h_bridge u
    h_deg6 (fun d hd => by have := h_nb8 d hd; omega)

/-- Primal–Dual Discharging Theorem on `H.dual` (`deg(u) ≥ 10`, neighbors `≥ 6`). -/
theorem dual_finalCharge_le_zero_of_deg_ge_10_of_isBridgeless_of_neighbors_deg_ge_6 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b fuel : Nat} (h_le_b : darts.length ≤ fuel_b) (h_le : darts.length ≤ fuel)
    (h_bridge : Hypermap.isBridgeless H darts fuel_b) (u : H.Dart)
    (h_deg10 : 10 ≤ Hypermap.nodeDegree H.dual u fuel)
    (h_nb6 : ∀ d ∈ getOrbit H.dual.node fuel u, 6 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f d) fuel) :
    finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0 := by
  have h_loopless : ∀ d ∈ getOrbit H.dual.node fuel u, Hypermap.sameVertex H.dual (H.dual.edge.f d) u fuel = false :=
    dual_loopless_orbit_of_isBridgeless H darts h_all h_le_b h_le h_bridge u
  exact finalCharge_le_zero_of_deg_ge_10_of_neighbors_deg_ge_6 H.dual darts h_all h_le u h_loopless h_deg10 h_nb6

/-!
### Stage H.1: Unconditional Degree-8 & Non-Degree-7 Outflow Bounds & `b1 = (7, 7)` Mutual-Exclusion Clique
-/

/-- Unconditional Degree-8 Half-Outflow Bound (`≤ 2` for ANY `degs : Nat → Nat`):
    among the 6 rules `[r57, r59, r61, r63, r64, r66]` with `b0 = 8`:
    - `r57..r64` require `degs 2 = 5`, while `r66` requires `degs 2 = 6`.
    - When `degs 2 ≤ 5`, `r66` vanishes and `[r57, r59, r61, r63, r64]` have sum `≤ 2`
      (`r57, r63, r64` conflict pairwise at `12, 13` and `r59, r61` conflict at `5`).
    - When `6 ≤ degs 2`, `r57..r64` all vanish, leaving at most `r66` (`≤ 1 ≤ 2`). -/
theorem orientOutflowDegs_le_2_of_deg_8 (inv : Bool) (degs : Nat → Nat)
    (hb0 : degs 0 = 8) :
    orientOutflowDegs inv degs ≤ 2 := by
  rw [orientOutflowDegs_eq_filter_active inv degs 8 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 8 0) = [r57, r59, r61, r63, r64, r66] := rfl
  rw [h_filt]; dsimp only [List.foldl]
  by_cases h2 : degs 2 ≤ 5
  · have h66 : matchesRawRuleDegs degs r66 = false :=
      not_matchesRawRuleDegs_of_triple_lt degs r66 2 6 6 (by decide) (by decide) (by omega)
    by_cases h12 : degs 12 ≤ 5
    · have h63 : matchesRawRuleDegs degs r63 = false :=
        not_matchesRawRuleDegs_of_triple_lt degs r63 12 6 12 (by decide) (by decide) (by omega)
      have h64 : matchesRawRuleDegs degs r64 = false :=
        not_matchesRawRuleDegs_of_triple_lt degs r64 12 6 12 (by decide) (by decide) (by omega)
      have hc57_61 := conflict_pair_at inv degs r57 r61 5 5 5 6 6 (by decide) (by decide) (by decide) (by decide)
      have h59 : (if (if inv then r59.invert else true) && matchesRawRuleDegs degs r59 then (1 : Int) else 0) ≤ 1 := by split <;> omega
      rw [h66, h63, h64]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
    · have h57 : matchesRawRuleDegs degs r57 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r57 12 5 5 (by decide) (by decide) (by omega)
      have h59 : matchesRawRuleDegs degs r59 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r59 12 5 5 (by decide) (by decide) (by omega)
      have hc63_64 := conflict_pair_at inv degs r63 r64 9 5 5 6 12 (by decide) (by decide) (by decide) (by decide)
      have h61 : (if (if inv then r61.invert else true) && matchesRawRuleDegs degs r61 then (1 : Int) else 0) ≤ 1 := by split <;> omega
      rw [h66, h57, h59]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
  · have h57 : matchesRawRuleDegs degs r57 = false :=
      not_matchesRawRuleDegs_of_triple_gt degs r57 2 5 5 (by decide) (by decide) (by omega)
    have h59 : matchesRawRuleDegs degs r59 = false :=
      not_matchesRawRuleDegs_of_triple_gt degs r59 2 5 5 (by decide) (by decide) (by omega)
    have h61 : matchesRawRuleDegs degs r61 = false :=
      not_matchesRawRuleDegs_of_triple_gt degs r61 2 5 5 (by decide) (by decide) (by omega)
    have h63 : matchesRawRuleDegs degs r63 = false :=
      not_matchesRawRuleDegs_of_triple_gt degs r63 2 5 5 (by decide) (by decide) (by omega)
    have h64 : matchesRawRuleDegs degs r64 = false :=
      not_matchesRawRuleDegs_of_triple_gt degs r64 2 5 5 (by decide) (by decide) (by omega)
    have h66 : (if (if inv then r66.invert else true) && matchesRawRuleDegs degs r66 then (1 : Int) else 0) ≤ 1 := by split <;> omega
    rw [h57, h59, h61, h63, h64]; simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- Any dart `d` at a degree-8 vertex sends at most `4` units of rule outflow (unconditional on target degree!). -/
theorem dartRuleOutflow_le_4_of_deg_8 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart) (h_d : Hypermap.nodeDegree H d fuel = 8) :
    dartRuleOutflow H fuel d ≤ 4 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have hf := orientOutflowDegs_le_2_of_deg_8 false
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H false d k) fuel) (by simpa using h_d)
  have ht := orientOutflowDegs_le_2_of_deg_8 true
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H true d k) fuel) (by simpa using h_d)
  omega

/-- Universal Per-Dart Outflow Bound for Non-Degree-7 Sources (`≤ 6`, unconditional on target degree!). -/
theorem dartRuleOutflow_le_6_of_deg_ne_7 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart) (h_ne7 : Hypermap.nodeDegree H d fuel ≠ 7) :
    dartRuleOutflow H fuel d ≤ 6 := by
  rcases Nat.lt_or_ge (Hypermap.nodeDegree H d fuel) 5 with hlt5 | hge5
  · have := dartRuleOutflow_eq_zero_of_deg_lt_5 H fuel d hlt5; omega
  · rcases Nat.lt_or_ge 8 (Hypermap.nodeDegree H d fuel) with hgt8 | hle8
    · have := dartRuleOutflow_eq_zero_of_deg_ge_9 H fuel d hgt8; omega
    · have h_cases : Hypermap.nodeDegree H d fuel = 5 ∨ Hypermap.nodeDegree H d fuel = 6 ∨
          Hypermap.nodeDegree H d fuel = 7 ∨ Hypermap.nodeDegree H d fuel = 8 := by omega
      rcases h_cases with h5 | h6 | h7 | h8
      · exact dartRuleOutflow_le_6_of_deg_5 H fuel d h5
      · exact dartRuleOutflow_le_6_of_deg_6 H fuel d h6
      · contradiction
      · have := dartRuleOutflow_le_4_of_deg_8 H fuel d h8; omega

/-- Mutual-exclusion clique for the 6 degree-7 rules `[r37, r43, r45, r49, r53, r55]` with `b1 = (7, 7)`:
    for ANY `degs : Nat → Nat`, at most 1 of these 6 rules can match `degs`! -/
private theorem deg7_b1_eq_7_clique_le_1 (inv : Bool) (degs : Nat → Nat) :
    (if (if inv then r37.invert else true) && matchesRawRuleDegs degs r37 then (1 : Int) else 0) +
    (if (if inv then r43.invert else true) && matchesRawRuleDegs degs r43 then (1 : Int) else 0) +
    (if (if inv then r45.invert else true) && matchesRawRuleDegs degs r45 then (1 : Int) else 0) +
    (if (if inv then r49.invert else true) && matchesRawRuleDegs degs r49 then (1 : Int) else 0) +
    (if (if inv then r53.invert else true) && matchesRawRuleDegs degs r53 then (1 : Int) else 0) +
    (if (if inv then r55.invert else true) && matchesRawRuleDegs degs r55 then (1 : Int) else 0) ≤ 1 := by
  by_cases h3 : degs 3 ≤ 5
  · have h43 : matchesRawRuleDegs degs r43 = false :=
      not_matchesRawRuleDegs_of_triple_lt degs r43 3 6 12 (by decide) (by decide) (by omega)
    have h45 : matchesRawRuleDegs degs r45 = false :=
      not_matchesRawRuleDegs_of_triple_lt degs r45 3 6 12 (by decide) (by decide) (by omega)
    have h49 : matchesRawRuleDegs degs r49 = false :=
      not_matchesRawRuleDegs_of_triple_lt degs r49 3 7 12 (by decide) (by decide) (by omega)
    have h53 : matchesRawRuleDegs degs r53 = false :=
      not_matchesRawRuleDegs_of_triple_lt degs r53 3 7 12 (by decide) (by decide) (by omega)
    have h55 : matchesRawRuleDegs degs r55 = false :=
      not_matchesRawRuleDegs_of_triple_lt degs r55 3 7 7 (by decide) (by decide) (by omega)
    have h37 : (if (if inv then r37.invert else true) && matchesRawRuleDegs degs r37 then (1 : Int) else 0) ≤ 1 := by split <;> omega
    rw [h43, h45, h49, h53, h55]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
  · have h37 : matchesRawRuleDegs degs r37 = false :=
      not_matchesRawRuleDegs_of_triple_gt degs r37 3 5 5 (by decide) (by decide) (by omega)
    by_cases h2 : degs 2 ≤ 5
    · have h43 : matchesRawRuleDegs degs r43 = false :=
        not_matchesRawRuleDegs_of_triple_lt degs r43 2 6 6 (by decide) (by decide) (by omega)
      have h45 : matchesRawRuleDegs degs r45 = false :=
        not_matchesRawRuleDegs_of_triple_lt degs r45 2 6 6 (by decide) (by decide) (by omega)
      have h53 : matchesRawRuleDegs degs r53 = false :=
        not_matchesRawRuleDegs_of_triple_lt degs r53 2 6 6 (by decide) (by decide) (by omega)
      have h55 : matchesRawRuleDegs degs r55 = false :=
        not_matchesRawRuleDegs_of_triple_lt degs r55 2 6 6 (by decide) (by decide) (by omega)
      have h49 : (if (if inv then r49.invert else true) && matchesRawRuleDegs degs r49 then (1 : Int) else 0) ≤ 1 := by split <;> omega
      rw [h37, h43, h45, h53, h55]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
    · have h49 : matchesRawRuleDegs degs r49 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r49 2 5 5 (by decide) (by decide) (by omega)
      by_cases h6 : degs 6 ≤ 5
      · have h55 : matchesRawRuleDegs degs r55 = false :=
          not_matchesRawRuleDegs_of_triple_lt degs r55 6 6 6 (by decide) (by decide) (by omega)
        by_cases h12 : degs 12 ≤ 5
        · have h45 : matchesRawRuleDegs degs r45 = false :=
            not_matchesRawRuleDegs_of_triple_lt degs r45 12 6 6 (by decide) (by decide) (by omega)
          have h53 : matchesRawRuleDegs degs r53 = false :=
            not_matchesRawRuleDegs_of_triple_lt degs r53 12 6 6 (by decide) (by decide) (by omega)
          have h43 : (if (if inv then r43.invert else true) && matchesRawRuleDegs degs r43 then (1 : Int) else 0) ≤ 1 := by split <;> omega
          rw [h37, h49, h55, h45, h53]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
        · have h43 : matchesRawRuleDegs degs r43 = false :=
            not_matchesRawRuleDegs_of_triple_gt degs r43 12 5 5 (by decide) (by decide) (by omega)
          have hc45_53 := conflict_pair_at inv degs r45 r53 4 5 5 6 6 (by decide) (by decide) (by decide) (by decide)
          rw [h37, h49, h55, h43]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
      · have h43 : matchesRawRuleDegs degs r43 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r43 6 5 5 (by decide) (by decide) (by omega)
        have h45 : matchesRawRuleDegs degs r45 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r45 6 5 5 (by decide) (by decide) (by omega)
        have h53 : matchesRawRuleDegs degs r53 = false :=
          not_matchesRawRuleDegs_of_triple_gt degs r53 6 5 5 (by decide) (by decide) (by omega)
        have h55 : (if (if inv then r55.invert else true) && matchesRawRuleDegs degs r55 then (1 : Int) else 0) ≤ 1 := by split <;> omega
        rw [h37, h49, h43, h45, h53]; simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- Unconditional Degree-7 Half-Outflow Bound (`≤ 5` in `inv = false`, for ANY `degs : Nat → Nat`). -/
theorem orientOutflowDegs_false_le_5_of_deg_7 (degs : Nat → Nat)
    (hb0 : degs 0 = 7) :
    orientOutflowDegs false degs ≤ 5 := by
  rw [orientOutflowDegs_eq_filter_active false degs 7 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 7 0) =
    [r17, r19, r21, r22, r24, r26, r27, r29, r31, r33, r35, r37, r39, r41, r43, r45, r47, r49, r51, r53, r55] := rfl
  rw [h_filt]; dsimp only [List.foldl]
  have hc1 := deg7_b1_ge_8_clique1_le_1 false degs
  have hc2 := conflict_pair_at false degs r19 r51 3 5 6 7 7 (by decide) (by decide) (by decide) (by decide)
  have hc3 := deg7_b1_ge_8_clique3_le_1 false degs
  have hc4 : (if (if false then r21.invert else true) && matchesRawRuleDegs degs r21 then (1 : Int) else 0) ≤ 1 := by split <;> omega
  have hc5 := deg7_b1_eq_7_clique_le_1 false degs
  omega

/-- Unconditional Degree-7 Half-Outflow Bound (`≤ 4` in `inv = true`, for ANY `degs : Nat → Nat`). -/
theorem orientOutflowDegs_true_le_4_of_deg_7 (degs : Nat → Nat)
    (hb0 : degs 0 = 7) :
    orientOutflowDegs true degs ≤ 4 := by
  rw [orientOutflowDegs_eq_filter_active true degs 7 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 7 0) =
    [r17, r19, r21, r22, r24, r26, r27, r29, r31, r33, r35, r37, r39, r41, r43, r45, r47, r49, r51, r53, r55] := rfl
  rw [h_filt]; dsimp only [List.foldl]
  have hc1 := deg7_b1_ge_8_clique1_le_1 true degs
  have hc2 := conflict_pair_at true degs r19 r51 3 5 6 7 7 (by decide) (by decide) (by decide) (by decide)
  have hc3 := deg7_b1_ge_8_clique3_le_1 true degs
  have hc4 : (if (if true then r21.invert else true) && matchesRawRuleDegs degs r21 then (1 : Int) else 0) = 0 := by
    have : r21.invert = false := rfl
    rw [this]; simp
  have hc5 := deg7_b1_eq_7_clique_le_1 true degs
  omega

/-- Any dart `d` at a degree-7 vertex sends at most `9` units of rule outflow (unconditional on target degree!). -/
theorem dartRuleOutflow_le_9_of_deg_7 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart) (h_d : Hypermap.nodeDegree H d fuel = 7) :
    dartRuleOutflow H fuel d ≤ 9 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have hf := orientOutflowDegs_false_le_5_of_deg_7
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H false d k) fuel) (by simpa using h_d)
  have ht := orientOutflowDegs_true_le_4_of_deg_7
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H true d k) fuel) (by simpa using h_d)
  omega

/-- Universal Per-Dart Outflow Bound (`≤ 9`) for ANY dart `d` in ANY hypermap `H`
    (unconditional on both source and target degree!). -/
theorem dartRuleOutflow_le_9 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart) :
    dartRuleOutflow H fuel d ≤ 9 := by
  rcases Nat.lt_or_ge (Hypermap.nodeDegree H d fuel) 5 with hlt5 | hge5
  · have := dartRuleOutflow_eq_zero_of_deg_lt_5 H fuel d hlt5; omega
  · rcases Nat.lt_or_ge 8 (Hypermap.nodeDegree H d fuel) with hgt8 | hle8
    · have := dartRuleOutflow_eq_zero_of_deg_ge_9 H fuel d hgt8; omega
    · have h_cases : Hypermap.nodeDegree H d fuel = 5 ∨ Hypermap.nodeDegree H d fuel = 6 ∨
          Hypermap.nodeDegree H d fuel = 7 ∨ Hypermap.nodeDegree H d fuel = 8 := by omega
      rcases h_cases with h5 | h6 | h7 | h8
      · have := dartRuleOutflow_le_6_of_deg_5 H fuel d h5; omega
      · have := dartRuleOutflow_le_6_of_deg_6 H fuel d h6; omega
      · exact dartRuleOutflow_le_9_of_deg_7 H fuel d h7
      · have := dartRuleOutflow_le_4_of_deg_8 H fuel d h8; omega

/-!
### Stage H.2: Faithful Outgoing-Spoke Identities & Enhanced Degree-5 Outflow Lower Bounds
-/

/-- Exact evaluation of `ruleVertexDart H inv d 4`: two `ruleRotInv H inv` steps around `0 = d`. -/
theorem ruleVertexDart_four (H : Hypermap) (inv : Bool) (d : H.Dart) :
    ruleVertexDart H inv d 4 = H.edge.f (ruleRotInv H inv (ruleRotInv H inv d)) := rfl

/-- Exact evaluation of `ruleVertexDart H inv d 5`: two `ruleRot H inv` steps around `0 = d`. -/
theorem ruleVertexDart_five (H : Hypermap) (inv : Bool) (d : H.Dart) :
    ruleVertexDart H inv d 5 = H.edge.f (ruleRot H inv (ruleRot H inv d)) := rfl

/-- Exact evaluation of `ruleVertexDart H inv d 12`: three `ruleRotInv H inv` steps around `0 = d`. -/
theorem ruleVertexDart_twelve (H : Hypermap) (inv : Bool) (d : H.Dart) :
    ruleVertexDart H inv d 12 = H.edge.f (ruleRotInv H inv (ruleRotInv H inv (ruleRotInv H inv d))) := rfl

/-- Exact evaluation of `ruleVertexDart H inv d 13`: four `ruleRotInv H inv` steps around `0 = d`. -/
theorem ruleVertexDart_thirteen (H : Hypermap) (inv : Bool) (d : H.Dart) :
    ruleVertexDart H inv d 13 =
      H.edge.f (ruleRotInv H inv (ruleRotInv H inv (ruleRotInv H inv (ruleRotInv H inv d)))) := rfl

/-- Exact evaluation of `ruleVertexDart H inv d 14`: three `ruleRot H inv` steps around `0 = d`. -/
theorem ruleVertexDart_fourteen (H : Hypermap) (inv : Bool) (d : H.Dart) :
    ruleVertexDart H inv d 14 = H.edge.f (ruleRot H inv (ruleRot H inv (ruleRot H inv d))) := rfl

/-- When `degs 0 = 5`, `7 ≤ degs 1`, and `degs 3 = 5`, both `r1` and `r3` fire in orientation `inv`,
    so `2 ≤ orientOutflowDegs inv degs` (with NO assumption on `degs 5`). -/
theorem two_le_orientOutflowDegs_of_deg_5_of_target_deg_ge_7_of_deg3_5 (inv : Bool) (degs : Nat → Nat)
    (hb0 : degs 0 = 5) (hb1 : 7 ≤ degs 1) (hb3 : degs 3 = 5) :
    2 ≤ orientOutflowDegs inv degs := by
  rw [orientOutflowDegs_eq_filter_active inv degs 5 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 5 0) = [r1, r3, r5] := rfl
  rw [h_filt]; dsimp only [List.foldl]
  have hr1 : matchesRawRuleDegs degs r1 = true := by
    dsimp [matchesRawRuleDegs, r1, degMatchesBound]
    rw [hb0, decide_eq_true (by omega : 5 ≤ degs 1)]
    rfl
  have hr3 : matchesRawRuleDegs degs r3 = true := by
    dsimp [matchesRawRuleDegs, r3, List.all, degMatchesBound]
    rw [hb0, hb3, decide_eq_true hb1]
    rfl
  have h_inv1 : (if inv then r1.invert else true) = true := by cases inv <;> rfl
  have h_inv3 : (if inv then r3.invert else true) = true := by cases inv <;> rfl
  have h5 : 0 ≤ (if (if inv then r5.invert else true) && matchesRawRuleDegs degs r5 then (1 : Int) else 0) := by split <;> omega
  rw [hr1, hr3, h_inv1, h_inv3]; dsimp; omega

/-- When `degs 0 = 5`, `6 ≤ degs 1`, `5 ≤ degs 3`, `degs 3 ≤ 6`, and `degs 5 = 5`,
    both `r1` and `r5` fire in orientation `inv`, so `2 ≤ orientOutflowDegs inv degs`. -/
theorem two_le_orientOutflowDegs_of_deg_5_of_target_deg_ge_6_of_deg3_in_5_6_of_deg5_5 (inv : Bool) (degs : Nat → Nat)
    (hb0 : degs 0 = 5) (hb1 : 6 ≤ degs 1) (hb3_lo : 5 ≤ degs 3) (hb3_hi : degs 3 ≤ 6) (hb5 : degs 5 = 5) :
    2 ≤ orientOutflowDegs inv degs := by
  rw [orientOutflowDegs_eq_filter_active inv degs 5 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 5 0) = [r1, r3, r5] := rfl
  rw [h_filt]; dsimp only [List.foldl]
  have hr1 : matchesRawRuleDegs degs r1 = true := by
    dsimp [matchesRawRuleDegs, r1, degMatchesBound]
    rw [hb0, decide_eq_true (by omega : 5 ≤ degs 1)]
    rfl
  have hr5 : matchesRawRuleDegs degs r5 = true := by
    dsimp [matchesRawRuleDegs, r5, List.all, degMatchesBound]
    rw [hb0, hb5, decide_eq_true hb1, decide_eq_true hb3_lo, decide_eq_true hb3_hi]
    rfl
  have h_inv1 : (if inv then r1.invert else true) = true := by cases inv <;> rfl
  have h_inv5 : (if inv then r5.invert else true) = true := by cases inv <;> rfl
  have h3 : 0 ≤ (if (if inv then r3.invert else true) && matchesRawRuleDegs degs r3 then (1 : Int) else 0) := by split <;> omega
  rw [hr1, hr5, h_inv1, h_inv5]; dsimp; omega

/-- When `degs 0 = 5`, `7 ≤ degs 1`, `degs 3 = 5`, and `degs 5 = 5`,
    all three rules `r1, r3, r5` fire in orientation `inv`, so `orientOutflowDegs inv degs = 3`. -/
theorem orientOutflowDegs_eq_3_of_deg_5_of_target_deg_ge_7_of_deg3_5_of_deg5_5 (inv : Bool) (degs : Nat → Nat)
    (hb0 : degs 0 = 5) (hb1 : 7 ≤ degs 1) (hb3 : degs 3 = 5) (hb5 : degs 5 = 5) :
    orientOutflowDegs inv degs = 3 := by
  rw [orientOutflowDegs_eq_filter_active inv degs 5 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 5 0) = [r1, r3, r5] := rfl
  rw [h_filt]; dsimp only [List.foldl]
  have hr1 : matchesRawRuleDegs degs r1 = true := by
    dsimp [matchesRawRuleDegs, r1, degMatchesBound]
    rw [hb0, decide_eq_true (by omega : 5 ≤ degs 1)]
    rfl
  have hr3 : matchesRawRuleDegs degs r3 = true := by
    dsimp [matchesRawRuleDegs, r3, List.all, degMatchesBound]
    rw [hb0, hb3, decide_eq_true hb1]
    rfl
  have hr5 : matchesRawRuleDegs degs r5 = true := by
    dsimp [matchesRawRuleDegs, r5, List.all, degMatchesBound]
    rw [hb0, hb3, hb5, decide_eq_true (by omega : 6 ≤ degs 1)]
    rfl
  have h_inv1 : (if inv then r1.invert else true) = true := by cases inv <;> rfl
  have h_inv3 : (if inv then r3.invert else true) = true := by cases inv <;> rfl
  have h_inv5 : (if inv then r5.invert else true) = true := by cases inv <;> rfl
  rw [hr1, hr3, hr5, h_inv1, h_inv3, h_inv5]; rfl

/-!
### Stage H.3: Refined Hub-Neighbor Vanishing (`deg3 ≥ 7`) & Discharging for Degree `≥ 8` Without Consecutive Degree-6 Neighbors
-/

/-- Faithful RSST Single-Side Flanking Vanishing Under Hub-Neighbors `≥ 6`:
    if `6 ≤ degs 0`, `6 ≤ degs 2`, `7 ≤ degs 3`, `6 ≤ degs 6`, and `6 ≤ degs 15`,
    then `orientOutflowDegs inv degs = 0`!
    - For `b0 ≥ 8`: vanishes since `6 ≤ degs 2` and `6 ≤ degs 6`.
    - For `b0 = 7`: `6 ≤ degs 2, 3, 6, 15` kills all rules except `{r17, r19, r41}`,
      and `r17, r19, r41` all require `degs 3 ≤ 6`, so `7 ≤ degs 3` kills them too!
    - For `b0 = 6`: all 7 rules `r3..r15` require `degs 3 ≤ 6`, so `7 ≤ degs 3` kills all 7! -/
theorem orientOutflowDegs_eq_zero_of_deg_ge_6_of_hub_neighbors_ge_6_of_deg3_ge_7 (inv : Bool) (degs : Nat → Nat)
    (hb0 : 6 ≤ degs 0) (hb2 : 6 ≤ degs 2) (hb3 : 7 ≤ degs 3)
    (hb6 : 6 ≤ degs 6) (hb15 : 6 ≤ degs 15) :
    orientOutflowDegs inv degs = 0 := by
  rcases Nat.lt_or_ge 7 (degs 0) with hge8 | hle7
  · exact orientOutflowDegs_eq_zero_of_deg_ge_8_of_deg2_ge_6_of_deg6_ge_6 inv degs hge8 hb2 hb6
  · have h_cases : degs 0 = 6 ∨ degs 0 = 7 := by omega
    rcases h_cases with h6 | h7
    · rw [orientOutflowDegs_eq_filter_active inv degs 6 0 h6 (Nat.zero_le _)]
      have h_filt : theRules.filter (ruleActiveFor 6 0) = [r3, r5, r7, r9, r11, r13, r15] := rfl
      rw [h_filt]; dsimp only [List.foldl]
      have h3 : matchesRawRuleDegs degs r3 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r3 3 5 5 (by decide) (by decide) (by omega)
      have h5 : matchesRawRuleDegs degs r5 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r5 3 5 6 (by decide) (by decide) (by omega)
      have h7' : matchesRawRuleDegs degs r7 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r7 3 5 5 (by decide) (by decide) (by omega)
      have h9 : matchesRawRuleDegs degs r9 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r9 3 6 6 (by decide) (by decide) (by omega)
      have h11 : matchesRawRuleDegs degs r11 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r11 3 6 6 (by decide) (by decide) (by omega)
      have h13 : matchesRawRuleDegs degs r13 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r13 3 5 5 (by decide) (by decide) (by omega)
      have h15 : matchesRawRuleDegs degs r15 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r15 3 6 6 (by decide) (by decide) (by omega)
      rw [h3, h5, h7', h9, h11, h13, h15]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
    · rw [orientOutflowDegs_eq_filter_active inv degs 7 0 h7 (Nat.zero_le _)]
      have h_filt : theRules.filter (ruleActiveFor 7 0) =
        [r17, r19, r21, r22, r24, r26, r27, r29, r31, r33, r35, r37, r39, r41, r43, r45, r47, r49, r51, r53, r55] := rfl
      rw [h_filt]; dsimp only [List.foldl]
      have h17 : matchesRawRuleDegs degs r17 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r17 3 5 6 (by decide) (by decide) (by omega)
      have h19 : matchesRawRuleDegs degs r19 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r19 3 5 6 (by decide) (by decide) (by omega)
      have h21 : matchesRawRuleDegs degs r21 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r21 3 5 5 (by decide) (by decide) (by omega)
      have h22 : matchesRawRuleDegs degs r22 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r22 3 5 5 (by decide) (by decide) (by omega)
      have h24 : matchesRawRuleDegs degs r24 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r24 3 5 5 (by decide) (by decide) (by omega)
      have h26 : matchesRawRuleDegs degs r26 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r26 3 5 5 (by decide) (by decide) (by omega)
      have h27 : matchesRawRuleDegs degs r27 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r27 3 5 5 (by decide) (by decide) (by omega)
      have h29 : matchesRawRuleDegs degs r29 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r29 3 5 5 (by decide) (by decide) (by omega)
      have h31 : matchesRawRuleDegs degs r31 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r31 3 5 5 (by decide) (by decide) (by omega)
      have h33 : matchesRawRuleDegs degs r33 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r33 3 5 5 (by decide) (by decide) (by omega)
      have h35 : matchesRawRuleDegs degs r35 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r35 3 5 5 (by decide) (by decide) (by omega)
      have h37 : matchesRawRuleDegs degs r37 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r37 3 5 5 (by decide) (by decide) (by omega)
      have h39 : matchesRawRuleDegs degs r39 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r39 3 5 5 (by decide) (by decide) (by omega)
      have h41 : matchesRawRuleDegs degs r41 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r41 3 6 6 (by decide) (by decide) (by omega)
      have h43 : matchesRawRuleDegs degs r43 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r43 6 5 5 (by decide) (by decide) (by omega)
      have h45 : matchesRawRuleDegs degs r45 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r45 6 5 5 (by decide) (by decide) (by omega)
      have h47 : matchesRawRuleDegs degs r47 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r47 2 5 5 (by decide) (by decide) (by omega)
      have h49 : matchesRawRuleDegs degs r49 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r49 2 5 5 (by decide) (by decide) (by omega)
      have h51 : matchesRawRuleDegs degs r51 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r51 2 5 5 (by decide) (by decide) (by omega)
      have h53 : matchesRawRuleDegs degs r53 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r53 6 5 5 (by decide) (by decide) (by omega)
      have h55 : matchesRawRuleDegs degs r55 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r55 15 5 5 (by decide) (by decide) (by omega)
      rw [h17, h19, h21, h22, h24, h26, h27, h29, h31, h33, h35, h37, h39, h41, h43, h45, h47, h49, h51, h53, h55]
      simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- Sharp per-spoke incoming outflow bound (`≤ 2`) when all neighbors of hub `u` have degree `≥ 6`
    and at least ONE of the two flanking spokes (`H.node.f d` or `H.node.inv d`) has neighbor degree `≥ 7`. -/
theorem dartRuleOutflow_le_2_of_mem_getOrbit_of_neighbors_deg_ge_6_of_flanking_spoke_ge_7 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u d : H.Dart}
    (hd : d ∈ getOrbit H.node fuel u)
    (h_nb6 : ∀ d' ∈ getOrbit H.node fuel u, 6 ≤ Hypermap.nodeDegree H (H.edge.f d') fuel)
    (h_flank7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel ∨
                7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel) :
    dartRuleOutflow H fuel (H.edge.f d) ≤ 2 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have h_rot : ∀ (inv : Bool) (d' : H.Dart), d' ∈ getOrbit H.node fuel u →
      ruleRot H inv d' ∈ getOrbit H.node fuel u :=
    fun inv d' hd' => getOrbit_closed_under_ruleRot_of_complete H darts h_all h_le hd' inv
  have h_rotInv : ∀ (inv : Bool) (d' : H.Dart), d' ∈ getOrbit H.node fuel u →
      ruleRotInv H inv d' ∈ getOrbit H.node fuel u :=
    fun inv d' hd' => getOrbit_closed_under_ruleRotInv_of_complete H darts h_all h_le hd' inv
  rcases h_flank7 with h_next7 | h_prev7
  · have hf := orientOutflowDegs_le_2_of_deg_ge_6_of_hub_neighbors_ge_6 false
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
      (by simpa [ruleVertexDart] using h_nb6 d hd)
      (by simpa [ruleVertexDart_edge_two] using h_nb6 _ (h_rot false d hd))
      (by simpa [ruleVertexDart_edge_three] using h_nb6 _ (h_rotInv false d hd))
      (by simpa [ruleVertexDart_edge_six] using h_nb6 _ (h_rot false _ (h_rot false d hd)))
      (by simpa [ruleVertexDart_edge_seven] using h_nb6 _ (h_rotInv false _ (h_rotInv false d hd)))
      (by simpa [ruleVertexDart_edge_fifteen] using h_nb6 _ (h_rot false _ (h_rot false _ (h_rot false d hd))))
    have ht := orientOutflowDegs_eq_zero_of_deg_ge_6_of_hub_neighbors_ge_6_of_deg3_ge_7 true
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
      (by simpa [ruleVertexDart] using h_nb6 d hd)
      (by simpa [ruleVertexDart_edge_two] using h_nb6 _ (h_rot true d hd))
      (by simpa [ruleVertexDart_true_edge_three] using h_next7)
      (by simpa [ruleVertexDart_edge_six] using h_nb6 _ (h_rot true _ (h_rot true d hd)))
      (by simpa [ruleVertexDart_edge_fifteen] using h_nb6 _ (h_rot true _ (h_rot true _ (h_rot true d hd))))
    omega
  · have hf := orientOutflowDegs_eq_zero_of_deg_ge_6_of_hub_neighbors_ge_6_of_deg3_ge_7 false
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
      (by simpa [ruleVertexDart] using h_nb6 d hd)
      (by simpa [ruleVertexDart_edge_two] using h_nb6 _ (h_rot false d hd))
      (by simpa [ruleVertexDart_false_edge_three] using h_prev7)
      (by simpa [ruleVertexDart_edge_six] using h_nb6 _ (h_rot false _ (h_rot false d hd)))
      (by simpa [ruleVertexDart_edge_fifteen] using h_nb6 _ (h_rot false _ (h_rot false _ (h_rot false d hd))))
    have ht := orientOutflowDegs_le_2_of_deg_ge_6_of_hub_neighbors_ge_6 true
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
      (by simpa [ruleVertexDart] using h_nb6 d hd)
      (by simpa [ruleVertexDart_edge_two] using h_nb6 _ (h_rot true d hd))
      (by simpa [ruleVertexDart_edge_three] using h_nb6 _ (h_rotInv true d hd))
      (by simpa [ruleVertexDart_edge_six] using h_nb6 _ (h_rot true _ (h_rot true d hd)))
      (by simpa [ruleVertexDart_edge_seven] using h_nb6 _ (h_rotInv true _ (h_rotInv true d hd)))
      (by simpa [ruleVertexDart_edge_fifteen] using h_nb6 _ (h_rot true _ (h_rot true _ (h_rot true d hd))))
    omega

/-- Global Discharging Theorem for Degree `≥ 8` when all neighbors have degree `≥ 6`
    and every spoke has at least one flanking neighbor of degree `≥ 7`:
    `initialCharge H u fuel + orbitNetShift H fuel u ≤ 0` (`60 - 10k + 2k = 60 - 8k ≤ -4 ≤ 0`). -/
theorem initialCharge_add_orbitNetShift_le_zero_of_deg_ge_8_of_neighbors_deg_ge_6_of_flanking_spoke_ge_7
    (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_deg8 : 8 ≤ Hypermap.nodeDegree H u fuel)
    (h_nb6 : ∀ d ∈ getOrbit H.node fuel u, 6 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel)
    (h_flank7 : ∀ d ∈ getOrbit H.node fuel u,
      7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel ∨
      7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel) :
    initialCharge H u fuel + orbitNetShift H fuel u ≤ 0 := by
  dsimp [initialCharge, orbitNetShift]
  have h_le_c := foldl_add_le_of_le_const (getOrbit H.node fuel u) (fun d => netDartShift H fuel d) 2 (by
    intro d hd
    dsimp [netDartShift]
    have h_out_nonneg : 0 ≤ dartRuleOutflow H fuel d := dartRuleOutflow_nonneg H fuel d
    have h_in2 : dartRuleOutflow H fuel (H.edge.f d) ≤ 2 :=
      dartRuleOutflow_le_2_of_mem_getOrbit_of_neighbors_deg_ge_6_of_flanking_spoke_ge_7 H darts h_all h_le hd
        h_nb6 (h_flank7 d hd)
    omega)
  dsimp at h_le_c
  have h_len : (getOrbit H.node fuel u).length = Hypermap.nodeDegree H u fuel := rfl
  omega

/-- Global Discharging Theorem for Degree `≥ 8` with `neighbors ≥ 6` and a degree-`≥ 7` flanking neighbor at each spoke. -/
theorem finalCharge_le_zero_of_deg_ge_8_of_neighbors_deg_ge_6_of_flanking_spoke_ge_7
    (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (h_deg8 : 8 ≤ Hypermap.nodeDegree H u fuel)
    (h_nb6 : ∀ d ∈ getOrbit H.node fuel u, 6 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel)
    (h_flank7 : ∀ d ∈ getOrbit H.node fuel u,
      7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel ∨
      7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel) :
    finalCharge H (rsstChargeShift H fuel) darts u ≤ 0 := by
  rw [finalCharge_eq_initialCharge_add_orbitNetShift H darts h_all h_le u h_loopless]
  exact initialCharge_add_orbitNetShift_le_zero_of_deg_ge_8_of_neighbors_deg_ge_6_of_flanking_spoke_ge_7
    H darts h_all h_le u h_deg8 h_nb6 h_flank7

/-- Primal–Dual Discharging Theorem on `H.dual` (`deg(u) ≥ 8`, neighbors `≥ 6`, flanking spoke `≥ 7`). -/
theorem dual_finalCharge_le_zero_of_deg_ge_8_of_isBridgeless_of_neighbors_deg_ge_6_of_flanking_spoke_ge_7
    (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b fuel : Nat} (h_le_b : darts.length ≤ fuel_b) (h_le : darts.length ≤ fuel)
    (h_bridge : Hypermap.isBridgeless H darts fuel_b) (u : H.Dart)
    (h_deg8 : 8 ≤ Hypermap.nodeDegree H.dual u fuel)
    (h_nb6 : ∀ d ∈ getOrbit H.dual.node fuel u, 6 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f d) fuel)
    (h_flank7 : ∀ d ∈ getOrbit H.dual.node fuel u,
      7 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f (H.dual.node.f d)) fuel ∨
      7 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f (H.dual.node.inv d)) fuel) :
    finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0 := by
  have h_loopless : ∀ d ∈ getOrbit H.dual.node fuel u, Hypermap.sameVertex H.dual (H.dual.edge.f d) u fuel = false :=
    dual_loopless_orbit_of_isBridgeless H darts h_all h_le_b h_le h_bridge u
  exact finalCharge_le_zero_of_deg_ge_8_of_neighbors_deg_ge_6_of_flanking_spoke_ge_7
    H.dual darts h_all h_le u h_loopless h_deg8 h_nb6 h_flank7

/-!
### Stage I.1: SWAR Cartwheel Bitmask Semantics (`degBitIdx`, `MatchesCartState`) & `testBit` Algebra
-/

/-- Maps a vertex degree `d` to its 5-bit lane index `0..4`:
    `0` for `d ≤ 5`, `1` for `d = 6`, `2` for `d = 7`, `3` for `d = 8`, `4` for `d ≥ 9`. -/
def degBitIdx (d : Nat) : Nat :=
  if d ≤ 5 then 0
  else if d == 6 then 1
  else if d == 7 then 2
  else if d == 8 then 3
  else 4

theorem degBitIdx_lt_5 (d : Nat) : degBitIdx d < 5 := by
  dsimp [degBitIdx]
  split <;> try omega
  split <;> try omega
  split <;> try omega
  split <;> omega

theorem degBitIdx_lt_6 (d : Nat) : degBitIdx d < 6 := by
  have := degBitIdx_lt_5 d; omega

theorem testBit_31_of_lt_5 {i : Nat} (hi : i < 5) : (31 : Nat).testBit i = true := by
  match i with
  | 0 | 1 | 2 | 3 | 4 => decide

theorem testBit_63_of_lt_6 {i : Nat} (hi : i < 6) : (63 : Nat).testBit i = true := by
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 => decide

theorem testBit_31_degBitIdx (d : Nat) : (31 : Nat).testBit (degBitIdx d) = true :=
  testBit_31_of_lt_5 (degBitIdx_lt_5 d)

theorem testBit_63_degBitIdx (d : Nat) : (63 : Nat).testBit (degBitIdx d) = true :=
  testBit_63_of_lt_6 (degBitIdx_lt_6 d)

/-- Exact `testBit` characterization of `getLaneNat st p` for bit indices `i < 6`. -/
theorem testBit_getLaneNat (st p : Nat) {i : Nat} (hi : i < 6) :
    (getLaneNat st p).testBit i = st.testBit (p * 6 + i) := by
  dsimp [getLaneNat]
  change ((st >>> (p * 6)) &&& 63).testBit i = st.testBit (p * 6 + i)
  rw [Nat.testBit_and, Nat.testBit_shiftRight, testBit_63_of_lt_6 hi, Bool.and_true]

set_option exponentiation.threshold 512 in
theorem testBit_all63Nat_of_lt {k : Nat} (hk : k < 360) : all63Nat.testBit k = true := by
  have h_eq : all63Nat = 2 ^ 360 - 1 := by decide
  rw [h_eq, Nat.testBit_two_pow_sub_one]
  exact decide_eq_true hk

theorem testBit_63_of_ge_6 {k : Nat} (hk : 6 ≤ k) : (63 : Nat).testBit k = false := by
  have h_eq : (63 : Nat) = 2 ^ 6 - 1 := rfl
  rw [h_eq, Nat.testBit_two_pow_sub_one]
  exact decide_eq_false (by omega)

/-- Exact `testBit` characterization of `setLaneNat st v val` at lane `v` (`v < 60`) for `i < 6`. -/
theorem testBit_getLaneNat_setLaneNat_self (st v val : Nat) (hv : v < 60) {i : Nat} (hi : i < 6) :
    (getLaneNat (setLaneNat st v val) v).testBit i = val.testBit i := by
  rw [testBit_getLaneNat _ v hi]
  dsimp [setLaneNat]
  change (((st &&& (all63Nat ^^^ (63 <<< (v * 6)))) ||| ((val &&& 63) <<< (v * 6)))).testBit (v * 6 + i) = val.testBit i
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_and]
  have hv_lt : v * 6 + i < 360 := by omega
  have h_ge : decide (v * 6 ≤ v * 6 + i) = true := decide_eq_true (by omega)
  have h_sub : v * 6 + i - v * 6 = i := by omega
  rw [testBit_all63Nat_of_lt hv_lt, h_ge, h_sub, testBit_63_of_lt_6 hi]
  simp

/-- Exact `testBit` characterization of `setLaneNat st v val` at lane `p ≠ v` (`p < 60`) for `i < 6`. -/
theorem testBit_getLaneNat_setLaneNat_ne (st v val p : Nat) (hp : p < 60) (hne : p ≠ v) {i : Nat} (hi : i < 6) :
    (getLaneNat (setLaneNat st v val) p).testBit i = (getLaneNat st p).testBit i := by
  rw [testBit_getLaneNat _ p hi, testBit_getLaneNat st p hi]
  dsimp [setLaneNat]
  change (((st &&& (all63Nat ^^^ (63 <<< (v * 6)))) ||| ((val &&& 63) <<< (v * 6)))).testBit (p * 6 + i) = st.testBit (p * 6 + i)
  rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_shiftLeft, Nat.testBit_shiftLeft, Nat.testBit_and]
  have hp_lt : p * 6 + i < 360 := by omega
  rw [testBit_all63Nat_of_lt hp_lt]
  by_cases hge : v * 6 ≤ p * 6 + i
  · have h_dec : decide (v * 6 ≤ p * 6 + i) = true := decide_eq_true hge
    have hge6 : 6 ≤ p * 6 + i - v * 6 := by omega
    rw [h_dec, testBit_63_of_ge_6 hge6]
    simp
  · have h_dec : decide (v * 6 ≤ p * 6 + i) = false := decide_eq_false hge
    rw [h_dec]
    simp

/-- A cartwheel degree assignment `cartDeg : Nat → Nat` matches SWAR state `st : Nat`
    at hub degree `deg` if for every cartwheel position `1 ≤ p ≤ 5 * deg`,
    the bit `degBitIdx (cartDeg p)` is set in lane `p`. -/
def MatchesCartState (deg : Nat) (cartDeg : Nat → Nat) (st : Nat) : Prop :=
  ∀ p, 1 ≤ p → p ≤ 5 * deg → (getLaneNat st p).testBit (degBitIdx (cartDeg p)) = true

/-- Partition soundness for `ProofTree.cond`:
    for any cartwheel degree assignment `cartDeg` matching `st` (`deg ≤ 11`), and any condition `(v, m)`,
    `cartDeg` matches either the true-branch state `stTrue` or the false-branch state `stFalse`. -/
theorem matchesCartState_cond_split (deg : Nat) (cartDeg : Nat → Nat) (st v : Nat) (m : Int)
    (h_deg : deg ≤ 11)
    (h_match : MatchesCartState deg cartDeg st) :
    let maskTrue := condMaskNat m
    let maskFalse := Nat.xor 31 maskTrue
    let curLane := getLaneNat st v
    MatchesCartState deg cartDeg (setLaneNat st v (Nat.land curLane maskTrue)) ∨
    MatchesCartState deg cartDeg (setLaneNat st v (Nat.land curLane maskFalse)) := by
  dsimp only
  by_cases hv : 1 ≤ v ∧ v ≤ 5 * deg
  · have hv60 : v < 60 := by omega
    have h_cur : (getLaneNat st v).testBit (degBitIdx (cartDeg v)) = true := h_match v hv.1 hv.2
    by_cases hm : (condMaskNat m).testBit (degBitIdx (cartDeg v)) = true
    · left
      intro p hp1 hp2
      have hp60 : p < 60 := by omega
      by_cases hpv : p = v
      · subst hpv
        rw [testBit_getLaneNat_setLaneNat_self _ _ _ hv60 (degBitIdx_lt_6 _)]
        change ((getLaneNat st p) &&& (condMaskNat m)).testBit (degBitIdx (cartDeg p)) = true
        rw [Nat.testBit_and, h_cur, hm]; rfl
      · rw [testBit_getLaneNat_setLaneNat_ne _ _ _ p hp60 hpv (degBitIdx_lt_6 _)]
        exact h_match p hp1 hp2
    · right
      intro p hp1 hp2
      have hp60 : p < 60 := by omega
      by_cases hpv : p = v
      · subst hpv
        rw [testBit_getLaneNat_setLaneNat_self _ _ _ hv60 (degBitIdx_lt_6 _)]
        change ((getLaneNat st p) &&& (31 ^^^ condMaskNat m)).testBit (degBitIdx (cartDeg p)) = true
        rw [Nat.testBit_and, Nat.testBit_xor, h_cur, testBit_31_degBitIdx]
        cases h_bit : (condMaskNat m).testBit (degBitIdx (cartDeg p))
        · rfl
        · contradiction
      · rw [testBit_getLaneNat_setLaneNat_ne _ _ _ p hp60 hpv (degBitIdx_lt_6 _)]
        exact h_match p hp1 hp2
  · left
    intro p hp1 hp2
    have hp60 : p < 60 := by omega
    have hpv : p ≠ v := by omega
    rw [testBit_getLaneNat_setLaneNat_ne _ _ _ p hp60 hpv (degBitIdx_lt_6 _)]
    exact h_match p hp1 hp2

/-!
### Stage I.2: `narrowSWAR` & `outletForcedSWAR` Bitwise Characterization
-/

/-- Exact `testBit` characterization of `narrowSWAR st po` (`Nat.land st po.keep`) for `i < 6`. -/
theorem testBit_getLaneNat_narrowSWAR (st : Nat) (po : FastPosOut) (p : Nat) {i : Nat} (hi : i < 6) :
    (getLaneNat (narrowSWAR st po) p).testBit i =
      ((getLaneNat st p).testBit i && (getLaneNat po.keep p).testBit i) := by
  rw [testBit_getLaneNat _ p hi, testBit_getLaneNat st p hi, testBit_getLaneNat po.keep p hi]
  dsimp [narrowSWAR]
  change (st &&& po.keep).testBit (p * 6 + i) = (st.testBit (p * 6 + i) && po.keep.testBit (p * 6 + i))
  rw [Nat.testBit_and]

/-- If `MatchesCartState deg cartDeg st` and `cartDeg` satisfies the keep-mask of `po` at every lane `1 ≤ p ≤ 5 * deg`,
    then `MatchesCartState deg cartDeg (narrowSWAR st po)`. -/
theorem matchesCartState_narrowSWAR (deg : Nat) (cartDeg : Nat → Nat) (st : Nat) (po : FastPosOut)
    (h_match : MatchesCartState deg cartDeg st)
    (h_keep : ∀ p, 1 ≤ p → p ≤ 5 * deg → (getLaneNat po.keep p).testBit (degBitIdx (cartDeg p)) = true) :
    MatchesCartState deg cartDeg (narrowSWAR st po) := by
  intro p hp1 hp2
  rw [testBit_getLaneNat_narrowSWAR st po p (degBitIdx_lt_6 _), h_match p hp1 hp2, h_keep p hp1 hp2]
  rfl

/-- If `outletForcedSWAR st po = true` (`Nat.land st po.forbid = 0`) and `MatchesCartState deg cartDeg st`,
    then no forbidden degree bit of `po.forbid` is set for `cartDeg` at any lane `1 ≤ p ≤ 5 * deg`. -/
theorem testBit_forbid_eq_false_of_outletForcedSWAR (deg : Nat) (cartDeg : Nat → Nat) (st : Nat) (po : FastPosOut)
    (h_match : MatchesCartState deg cartDeg st)
    (h_forced : outletForcedSWAR st po = true) :
    ∀ p, 1 ≤ p → p ≤ 5 * deg → (getLaneNat po.forbid p).testBit (degBitIdx (cartDeg p)) = false := by
  intro p hp1 hp2
  have h_zero : st &&& po.forbid = 0 := Nat.beq_eq.mp h_forced
  have h_tb : (st &&& po.forbid).testBit (p * 6 + degBitIdx (cartDeg p)) = false := by
    rw [h_zero, Nat.zero_testBit]
  rw [Nat.testBit_and, ← testBit_getLaneNat st p (degBitIdx_lt_6 _),
      ← testBit_getLaneNat po.forbid p (degBitIdx_lt_6 _), h_match p hp1 hp2, Bool.true_and] at h_tb
  exact h_tb

/-!
### Stage I.3: Inductive Leaf Extraction Theorem for `verifyTreePureRec`
-/

/-- Predicate characterizing that a SWAR state `st_leaf` reached at a leaf of `verifyTreePureRec`
    is verified by one of the three RSST leaf rules (`reduce`, `hubcap`, or `sym`). -/
def VerifiedCartLeaf (deg : Nat) (shiftedTable : List (List FastPosOut)) (st_leaf : Nat) : Prop :=
  (∃ hs_leaf, (reduceAxleRec deg 64 [st_leaf] hs_leaf).1 = true) ∨
  (∃ members hs_leaf, (verifyHubcapMembersRec deg st_leaf shiftedTable members hs_leaf).1 = true) ∨
  (∃ (k eps : Nat) (found : SymOutlet), (!Nat.ble deg k && Nat.ble eps 1) = true ∧
    symForcedRec st_leaf (Nat.add k 1) deg (!Nat.beq eps 0) found.conds = true)

/-- Fundamental Inductive Soundness of `verifyTreePureRec`:
    for any proof tree `t : ProofTree` and any cartwheel degree assignment `cartDeg : Nat → Nat`
    matching the current SWAR state `st`, if `(verifyTreePureRec deg shiftedTable t st lineno lev condV condM syms hs).1 = true`,
    then there exists a leaf state `st_leaf` matching `cartDeg` (`MatchesCartState deg cartDeg st_leaf`)
    that satisfies `VerifiedCartLeaf deg shiftedTable st_leaf`. -/
theorem exists_verifiedCartLeaf_of_verifyTreePureRec (deg : Nat) (shiftedTable : List (List FastPosOut))
    (t : ProofTree) (cartDeg : Nat → Nat) (h_deg : deg ≤ 11) :
    ∀ (st lineno lev condV condM : Nat) (syms : List SymOutlet) (hs : HintStream),
      MatchesCartState deg cartDeg st →
      (verifyTreePureRec deg shiftedTable t st lineno lev condV condM syms hs).1 = true →
      ∃ st_leaf : Nat, MatchesCartState deg cartDeg st_leaf ∧ VerifiedCartLeaf deg shiftedTable st_leaf := by
  induction t with
  | cond v m tTrue tFalse ihTrue ihFalse =>
    intro st lineno lev condV condM syms hs h_match h_ok
    rw [verifyTreePureRec_cond_eq] at h_ok
    simp only [strictNat_eq] at h_ok
    let maskTrue := condMaskNat m
    let maskFalse := Nat.xor 31 maskTrue
    let curLane := getLaneNat st v
    let stTrue := setLaneNat st v (Nat.land curLane maskTrue)
    let stFalse := setLaneNat st v (Nat.land curLane maskFalse)
    let lev1 := Nat.add lev 1
    let lineno1 := Nat.add lineno 1
    let syms' :=
      match extractCondsRec deg condV condM lev with
      | none => syms
      | some conds => { number := lineno, nolines := lev1, conds := conds } :: syms
    let condV' := setLaneNat (setLaneNat condV lev v) lev1 0
    let condM' := setLaneNat (setLaneNat condM lev maskTrue) lev1 0
    let resTrue := verifyTreePureRec deg shiftedTable tTrue stTrue lineno1 lev1 condV' condM' syms' hs
    change (@Bool.rec (fun _ => Bool × Nat × HintStream) (false, resTrue.2.fst, resTrue.2.snd)
      (verifyTreePureRec deg shiftedTable tFalse stFalse resTrue.2.fst lev condV' condM' syms' resTrue.2.snd)
      resTrue.fst).fst = true at h_ok
    cases h_b : resTrue.fst with
    | false =>
      rw [h_b] at h_ok
      dsimp at h_ok
      contradiction
    | true =>
      rw [h_b] at h_ok
      dsimp at h_ok
      rcases matchesCartState_cond_split deg cartDeg st v m h_deg h_match with h_mTrue | h_mFalse
      · exact ihTrue stTrue lineno1 lev1 condV' condM' syms' hs h_mTrue h_b
      · exact ihFalse stFalse resTrue.2.fst lev condV' condM' syms' resTrue.2.snd h_mFalse h_ok
  | reduce =>
    intro st lineno lev condV condM syms hs h_match h_ok
    change (let (ok, hs') := reduceAxleRec deg 64 [st] hs
            strictNat (Nat.add lineno 1) fun lineno' => (ok, lineno', hs')).1 = true at h_ok
    simp only [strictNat_eq] at h_ok
    exact ⟨st, h_match, Or.inl ⟨hs, h_ok⟩⟩
  | hubcap members =>
    intro st lineno lev condV condM syms hs h_match h_ok
    change (let (ok, hs') := verifyHubcapMembersRec deg st shiftedTable members hs
            strictNat (Nat.add lineno 1) fun lineno' => (ok, lineno', hs')).1 = true at h_ok
    simp only [strictNat_eq] at h_ok
    exact ⟨st, h_match, Or.inr (Or.inl ⟨members, hs, h_ok⟩)⟩
  | sym k eps lev_in line =>
    intro st lineno lev condV condM syms hs h_match h_ok
    change (let ok :=
              Bool.rec false
                (match findSymOutletRec line syms with
                 | none => false
                 | some found =>
                   Bool.rec false
                     (symForcedRec st (Nat.add k 1) deg (!Nat.beq eps 0) found.conds)
                     (Nat.beq found.nolines (Nat.add lev_in 1)))
                (!Nat.ble deg k && Nat.ble eps 1)
            strictNat (Nat.add lineno 1) fun lineno' => (ok, lineno', hs)).1 = true at h_ok
    simp only [strictNat_eq] at h_ok
    cases h_ke : (!Nat.ble deg k && Nat.ble eps 1) with
    | false =>
      rw [h_ke] at h_ok; dsimp at h_ok; contradiction
    | true =>
      rw [h_ke] at h_ok; dsimp at h_ok
      cases h_find : findSymOutletRec line syms with
      | none =>
        rw [h_find] at h_ok; contradiction
      | some found =>
        rw [h_find] at h_ok; dsimp at h_ok
        cases h_nl : Nat.beq found.nolines (Nat.add lev_in 1) with
        | false =>
          rw [h_nl] at h_ok; dsimp at h_ok; contradiction
        | true =>
          rw [h_nl] at h_ok; dsimp at h_ok
          exact ⟨st, h_match, Or.inr (Or.inr ⟨k, eps, found, h_ke, h_ok⟩)⟩

/-!
### Stage I.4: Top-Level `verifyTree` & `DischargingTreesVerified` Leaf Extraction
-/

theorem getLaneNat_initStateForDeg_eq_31 (deg : Nat)
    (h_deg : deg = 7 ∨ deg = 8 ∨ deg = 9 ∨ deg = 10 ∨ deg = 11)
    {p : Nat} (hp1 : 1 ≤ p) (hp2 : p ≤ 5 * deg) :
    getLaneNat (getInitStateForDeg deg) p = 31 := by
  rcases h_deg with rfl | rfl | rfl | rfl | rfl
  · have h_all : (List.range' 1 35).all (fun k => getLaneNat (getInitStateForDeg 7) k == 31) = true := by decide
    have h_mem : p ∈ List.range' 1 35 := List.mem_range'.mpr ⟨p - 1, by omega, by omega⟩
    exact beq_iff_eq.mp (List.all_eq_true.mp h_all p h_mem)
  · have h_all : (List.range' 1 40).all (fun k => getLaneNat (getInitStateForDeg 8) k == 31) = true := by decide
    have h_mem : p ∈ List.range' 1 40 := List.mem_range'.mpr ⟨p - 1, by omega, by omega⟩
    exact beq_iff_eq.mp (List.all_eq_true.mp h_all p h_mem)
  · have h_all : (List.range' 1 45).all (fun k => getLaneNat (getInitStateForDeg 9) k == 31) = true := by decide
    have h_mem : p ∈ List.range' 1 45 := List.mem_range'.mpr ⟨p - 1, by omega, by omega⟩
    exact beq_iff_eq.mp (List.all_eq_true.mp h_all p h_mem)
  · have h_all : (List.range' 1 50).all (fun k => getLaneNat (getInitStateForDeg 10) k == 31) = true := by decide
    have h_mem : p ∈ List.range' 1 50 := List.mem_range'.mpr ⟨p - 1, by omega, by omega⟩
    exact beq_iff_eq.mp (List.all_eq_true.mp h_all p h_mem)
  · have h_all : (List.range' 1 55).all (fun k => getLaneNat (getInitStateForDeg 11) k == 31) = true := by decide
    have h_mem : p ∈ List.range' 1 55 := List.mem_range'.mpr ⟨p - 1, by omega, by omega⟩
    exact beq_iff_eq.mp (List.all_eq_true.mp h_all p h_mem)

/-- Every cartwheel degree assignment `cartDeg : Nat → Nat` matches the initial SWAR state
    `getInitStateForDeg deg` for `deg ∈ {7, 8, 9, 10, 11}`. -/
theorem matchesCartState_getInitStateForDeg (deg : Nat) (cartDeg : Nat → Nat)
    (h_deg : deg = 7 ∨ deg = 8 ∨ deg = 9 ∨ deg = 10 ∨ deg = 11) :
    MatchesCartState deg cartDeg (getInitStateForDeg deg) := by
  intro p hp1 hp2
  rw [getLaneNat_initStateForDeg_eq_31 deg h_deg hp1 hp2]
  exact testBit_31_degBitIdx (cartDeg p)

/-- Top-level leaf extraction theorem for `verifyTree`:
    whenever `verifyTree configs deg A_low A_upp t outs = true` for `deg ∈ {7, 8, 9, 10, 11}`,
    every cartwheel degree assignment `cartDeg : Nat → Nat` matches a verified leaf `st_leaf` of `t`. -/
theorem exists_verifiedCartLeaf_of_verifyTree (configs : List Configuration) (deg : Nat)
    (A_low A_upp : Array Nat) (t : ProofTree) (outs : Array Outlet) (cartDeg : Nat → Nat)
    (h_deg : deg = 7 ∨ deg = 8 ∨ deg = 9 ∨ deg = 10 ∨ deg = 11)
    (h_ver : verifyTree configs deg A_low A_upp t outs = true) :
    ∃ st_leaf : Nat, MatchesCartState deg cartDeg st_leaf ∧
      VerifiedCartLeaf deg (getShiftedTableForDeg deg) st_leaf := by
  have h_le11 : deg ≤ 11 := by rcases h_deg with rfl | rfl | rfl | rfl | rfl <;> omega
  exact exists_verifiedCartLeaf_of_verifyTreePureRec deg (getShiftedTableForDeg deg) t cartDeg h_le11
    (getInitStateForDeg deg) 2 0 0 0 [] ([], getHintsForDeg deg)
    (matchesCartState_getInitStateForDeg deg cartDeg h_deg) h_ver

/-- Master Leaf Extraction Theorem from `DischargingTreesVerified`:
    Given `DischargingTreesVerified configs`, for every hub degree `deg ∈ {7, 8, 9, 10, 11}`
    and every cartwheel degree assignment `cartDeg : Nat → Nat`, there exists a leaf state `st_leaf`
    matching `cartDeg` that satisfies `VerifiedCartLeaf deg (getShiftedTableForDeg deg) st_leaf`. -/
theorem exists_verifiedCartLeaf_of_dischargingTreesVerified (configs : List Configuration)
    (h_trees : DischargingTreesVerified configs) (deg : Nat) (cartDeg : Nat → Nat)
    (h_deg : deg = 7 ∨ deg = 8 ∨ deg = 9 ∨ deg = 10 ∨ deg = 11) :
    ∃ st_leaf : Nat, MatchesCartState deg cartDeg st_leaf ∧
      VerifiedCartLeaf deg (getShiftedTableForDeg deg) st_leaf := by
  rcases h_trees with ⟨h7, h8, h9, h10, h11⟩
  rcases h_deg with rfl | rfl | rfl | rfl | rfl
  · exact exists_verifiedCartLeaf_of_verifyTree configs 7 (trivial_A_low 7) (trivial_A_upp 7) (present7 ()) (readOutlets 7 theRules) cartDeg (Or.inl rfl) h7
  · exact exists_verifiedCartLeaf_of_verifyTree configs 8 (trivial_A_low 8) (trivial_A_upp 8) (present8 ()) (readOutlets 8 theRules) cartDeg (Or.inr (Or.inl rfl)) h8
  · exact exists_verifiedCartLeaf_of_verifyTree configs 9 (trivial_A_low 9) (trivial_A_upp 9) (present9 ()) (readOutlets 9 theRules) cartDeg (Or.inr (Or.inr (Or.inl rfl))) h9
  · exact exists_verifiedCartLeaf_of_verifyTree configs 10 (trivial_A_low 10) (trivial_A_upp 10) (present10 ()) (readOutlets 10 theRules) cartDeg (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) h10
  · exact exists_verifiedCartLeaf_of_verifyTree configs 11 (trivial_A_low 11) (trivial_A_upp 11) (present11 ()) (readOutlets 11 theRules) cartDeg (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) h11

/-!
### Stage J.1: 6-Bit SWAR Lane Addition Without Carry & `outletPermittedSWAR` Soundness
-/

theorem land_63_eq_mod_64 (n : Nat) : n &&& 63 = n % 64 := by
  have h63 : (63 : Nat) = 2 ^ 6 - 1 := rfl
  rw [h63, Nat.and_two_pow_sub_one_eq_mod]

theorem getLaneNat_eq_div_mod (st p : Nat) :
    getLaneNat st p = (st / 2 ^ (p * 6)) % 64 := by
  dsimp [getLaneNat]
  change ((st >>> (p * 6)) &&& 63) = (st / 2 ^ (p * 6)) % 64
  rw [Nat.shiftRight_eq_div_pow, land_63_eq_mod_64]

theorem pow_succ_mul_six (p : Nat) : 2 ^ ((p + 1) * 6) = 2 ^ (p * 6) * 64 := by
  have h1 : (p + 1) * 6 = p * 6 + 6 := by omega
  rw [h1, Nat.pow_add]

theorem mod_pow_succ_mul_six (Z p : Nat) :
    Z % 2 ^ ((p + 1) * 6) = Z % 2 ^ (p * 6) + 2 ^ (p * 6) * getLaneNat Z p := by
  rw [pow_succ_mul_six, getLaneNat_eq_div_mod]
  let P := 2 ^ (p * 6)
  have h_pos : 0 < P := Nat.two_pow_pos (p * 6)
  have h1 := Nat.div_add_mod Z P
  have h2 := Nat.div_add_mod (Z / P) 64
  have h3 := Nat.mod_lt Z h_pos
  have h4 : (Z / P) % 64 < 64 := Nat.mod_lt _ (by omega)
  have h_mul_add : P * (64 * ((Z / P) / 64) + (Z / P) % 64) =
      (P * 64) * ((Z / P) / 64) + P * ((Z / P) % 64) := by
    rw [Nat.mul_add, ← Nat.mul_assoc, Nat.mul_comm P 64, Nat.mul_assoc]
  have h_eq : Z = (P * 64) * ((Z / P) / 64) + (Z % P + P * ((Z / P) % 64)) := by
    have h_div : P * (Z / P) = P * (64 * ((Z / P) / 64) + (Z / P) % 64) :=
      congrArg (P * ·) h2.symm
    omega
  have h_rem_lt : Z % P + P * ((Z / P) % 64) < P * 64 := by
    have h_le63 : (Z / P) % 64 ≤ 63 := by omega
    have h_mul_le : P * ((Z / P) % 64) ≤ P * 63 := Nat.mul_le_mul_left P h_le63
    omega
  have h_mod : ((P * 64) * ((Z / P) / 64) + (Z % P + P * ((Z / P) % 64))) % (P * 64) =
      Z % P + P * ((Z / P) % 64) := by
    rw [Nat.mul_add_mod, Nat.mod_eq_of_lt h_rem_lt]
  simpa [← h_eq] using h_mod

theorem mod_add_mod_lt_pow_mul_six (X Y : Nat) (hX : ∀ q, getLaneNat X q ≤ 31) (hY : ∀ q, getLaneNat Y q ≤ 31) :
    ∀ p, X % 2 ^ (p * 6) + Y % 2 ^ (p * 6) < 2 ^ (p * 6) := by
  intro p
  induction p with
  | zero =>
    change X % 1 + Y % 1 < 1
    omega
  | succ p ih =>
    rw [mod_pow_succ_mul_six X p, mod_pow_succ_mul_six Y p, pow_succ_mul_six]
    have hXp : 2 ^ (p * 6) * getLaneNat X p ≤ 2 ^ (p * 6) * 31 := Nat.mul_le_mul_left _ (hX p)
    have hYp : 2 ^ (p * 6) * getLaneNat Y p ≤ 2 ^ (p * 6) * 31 := Nat.mul_le_mul_left _ (hY p)
    omega

/-- Fundamental SWAR No-Carry Addition Theorem:
    When every 6-bit lane of `X` and `Y` is at most `31` (so bit 5, the guard bit `32`, is `0`),
    binary addition `X + Y` never carries across 6-bit lane boundaries:
    `getLaneNat (X + Y) p = getLaneNat X p + getLaneNat Y p` for every lane `p`. -/
theorem getLaneNat_add_of_le_31 (X Y : Nat)
    (hX : ∀ q, getLaneNat X q ≤ 31) (hY : ∀ q, getLaneNat Y q ≤ 31) (p : Nat) :
    getLaneNat (X + Y) p = getLaneNat X p + getLaneNat Y p := by
  have h_no_carry := mod_add_mod_lt_pow_mul_six X Y hX hY p
  have h_no_carry_succ := mod_add_mod_lt_pow_mul_six X Y hX hY (p + 1)
  have h_X_succ := mod_pow_succ_mul_six X p
  have h_Y_succ := mod_pow_succ_mul_six Y p
  have h_XY_succ := mod_pow_succ_mul_six (X + Y) p
  have h_pos : 0 < 2 ^ (p * 6) := Nat.two_pow_pos (p * 6)
  have h_mod_p : (X + Y) % 2 ^ (p * 6) = X % 2 ^ (p * 6) + Y % 2 ^ (p * 6) := by
    let P := 2 ^ (p * 6)
    have h1 := Nat.div_add_mod X P
    have h2 := Nat.div_add_mod Y P
    have h_dist := Nat.mul_add P (X / P) (Y / P)
    have h_eq : X + Y = P * (X / P + Y / P) + (X % P + Y % P) := by omega
    rw [h_eq, Nat.mul_add_mod, Nat.mod_eq_of_lt h_no_carry]
  have h_mod_succ : (X + Y) % 2 ^ ((p + 1) * 6) = X % 2 ^ ((p + 1) * 6) + Y % 2 ^ ((p + 1) * 6) := by
    let Q := 2 ^ ((p + 1) * 6)
    have h1 := Nat.div_add_mod X Q
    have h2 := Nat.div_add_mod Y Q
    have h_dist := Nat.mul_add Q (X / Q) (Y / Q)
    have h_eq : X + Y = Q * (X / Q + Y / Q) + (X % Q + Y % Q) := by omega
    rw [h_eq, Nat.mul_add_mod, Nat.mod_eq_of_lt h_no_carry_succ]
  rw [h_XY_succ, h_X_succ, h_Y_succ, h_mod_p] at h_mod_succ
  have h_dist := Nat.mul_add (2 ^ (p * 6)) (getLaneNat X p) (getLaneNat Y p)
  have h_mul_eq : 2 ^ (p * 6) * getLaneNat (X + Y) p = 2 ^ (p * 6) * (getLaneNat X p + getLaneNat Y p) := by omega
  exact Nat.eq_of_mul_eq_mul_left h_pos h_mul_eq

/-- Computable structural well-formedness predicate for a SWAR outlet `po : FastPosOut` at hub degree `deg`.
    Formulated purely with whole-word 360-bit SWAR operations (zero lane loops) for instantaneous kernel evaluation. -/
def validFastPosOut (deg : Nat) (po : FastPosOut) : Bool :=
  (po.mask == (po.keep &&& po.add)) &&
  (po.add &&& all31Nat == po.add) &&
  (po.high &&& (all63Nat ^^^ all31Nat) == po.high) &&
  (po.high &&& 63 == 0) &&
  (po.high >>> ((5 * deg + 1) * 6) == 0) &&
  (po.keep &&& all63Nat == (all31Nat ^^^ (po.forbid &&& all31Nat))) &&
  (po.add == ((po.high >>> 1) ||| (po.high >>> 2) ||| (po.high >>> 3) ||| (po.high >>> 4) ||| (po.high >>> 5)))

/-- An outlet `po : FastPosOut` is active on cartwheel degree assignment `cartDeg : Nat → Nat`
    at hub degree `deg` if no position `1 ≤ p ≤ 5 * deg` has its degree bit set in `po.forbid`. -/
def OutletActive (deg : Nat) (cartDeg : Nat → Nat) (po : FastPosOut) : Bool :=
  (List.range' 1 (5 * deg)).all (fun p =>
    !(getLaneNat po.forbid p).testBit (degBitIdx (cartDeg p)))

theorem getLaneNat_lt_64 (st p : Nat) : getLaneNat st p < 64 := by
  rw [getLaneNat_eq_div_mod]
  exact Nat.mod_lt _ (by omega)

theorem testBit_getLaneNat_of_ge_6 (st p : Nat) {i : Nat} (hi : 6 ≤ i) :
    (getLaneNat st p).testBit i = false := by
  dsimp [getLaneNat]
  change ((st >>> (p * 6)) &&& 63).testBit i = false
  rw [Nat.testBit_and, testBit_63_of_ge_6 hi, Bool.and_false]

theorem getLaneNat_and (X Y p : Nat) :
    getLaneNat (X &&& Y) p = (getLaneNat X p &&& getLaneNat Y p) := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 6
  · rw [testBit_getLaneNat _ p hi, Nat.testBit_and, Nat.testBit_and,
        testBit_getLaneNat X p hi, testBit_getLaneNat Y p hi]
  · have hi6 : 6 ≤ i := by omega
    rw [testBit_getLaneNat_of_ge_6 _ p hi6, Nat.testBit_and,
        testBit_getLaneNat_of_ge_6 X p hi6, Bool.false_and]

set_option exponentiation.threshold 512 in
theorem all31Nat_lt_two_pow_360 : all31Nat < 2 ^ 360 := by decide

set_option exponentiation.threshold 512 in
theorem getLaneNat_all31Nat_le_31 (p : Nat) : getLaneNat all31Nat p ≤ 31 := by
  by_cases hp : p < 60
  · have h_all : (List.range 60).all (fun q => getLaneNat all31Nat q == 31) = true := by decide
    have h_eq : getLaneNat all31Nat p = 31 :=
      beq_iff_eq.mp (List.all_eq_true.mp h_all p (List.mem_range.mpr hp))
    omega
  · have h_ge : 360 ≤ p * 6 := by omega
    have h_pow : 2 ^ 360 ≤ 2 ^ (p * 6) := Nat.pow_le_pow_right (by omega) h_ge
    have h_lt : all31Nat < 2 ^ (p * 6) := Nat.lt_of_lt_of_le all31Nat_lt_two_pow_360 h_pow
    rw [getLaneNat_eq_div_mod, Nat.div_eq_of_lt h_lt]
    omega

theorem getLaneNat_le_31_of_and_all31Nat (X : Nat) (hX : (X &&& all31Nat) = X) (p : Nat) :
    getLaneNat X p ≤ 31 := by
  rw [← hX, getLaneNat_and]
  exact Nat.le_trans Nat.and_le_right (getLaneNat_all31Nat_le_31 p)

set_option exponentiation.threshold 512 in
theorem testBit_all63Nat_of_ge_360 {k : Nat} (hk : 360 ≤ k) : all63Nat.testBit k = false := by
  have h_eq : all63Nat = 2 ^ 360 - 1 := by decide
  rw [h_eq, Nat.testBit_two_pow_sub_one]
  exact decide_eq_false (by omega)

set_option exponentiation.threshold 512 in
theorem testBit_all31Nat_of_ge_360 {k : Nat} (hk : 360 ≤ k) : all31Nat.testBit k = false := by
  have h_pow : 2 ^ 360 ≤ 2 ^ k := Nat.pow_le_pow_right (by omega) hk
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le all31Nat_lt_two_pow_360 h_pow)

theorem testBit_32_eq_true_iff {i : Nat} (hi : i < 6) :
    (32 : Nat).testBit i = true ↔ i = 5 := by
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 => decide

theorem testBit_add_31_five_of_testBit_lt_5 {m b : Nat} (hm : m ≤ 31) (_hb : b < 5)
    (h_bit : m.testBit b = true) : (m + 31).testBit 5 = true := by
  have hm_pos : 1 ≤ m := by
    by_cases h0 : m = 0
    · subst h0; simp at h_bit
    · omega
  have h_div : (m + 31) / 32 = 1 := by omega
  rw [Nat.testBit, Nat.shiftRight_eq_div_pow]
  change (1 &&& ((m + 31) / 32) != 0) = true
  rw [h_div]
  rfl

/-- Soundness 1: Any forced SWAR outlet (`outletForcedSWAR st po = true`) is active on `cartDeg`. -/
theorem outletActive_of_outletForcedSWAR (deg : Nat) (cartDeg : Nat → Nat) (st : Nat) (po : FastPosOut)
    (h_match : MatchesCartState deg cartDeg st)
    (h_forced : outletForcedSWAR st po = true) :
    OutletActive deg cartDeg po = true := by
  dsimp [OutletActive]
  rw [List.all_eq_true]
  intro p hp
  rcases List.mem_range'.mp hp with ⟨i, hi, hp_eq⟩
  have h_false := testBit_forbid_eq_false_of_outletForcedSWAR deg cartDeg st po h_match h_forced p (by omega) (by omega)
  rw [h_false]
  rfl

set_option exponentiation.threshold 512 in
theorem testBit_all31Nat_of_lt_360 (p : Nat) (hp : p < 60) {i : Nat} (hi : i < 6) :
    all31Nat.testBit (p * 6 + i) = (31 : Nat).testBit i := by
  have h_all : (List.range 60).all (fun q => getLaneNat all31Nat q == 31) = true := by decide
  have h_eq : getLaneNat all31Nat p = 31 :=
    beq_iff_eq.mp (List.all_eq_true.mp h_all p (List.mem_range.mpr hp))
  rw [← testBit_getLaneNat all31Nat p hi, h_eq]

theorem eq_31_of_le_31_of_testBits {a : Nat} (ha : a ≤ 31)
    (h0 : a.testBit 0 = true) (h1 : a.testBit 1 = true) (h2 : a.testBit 2 = true)
    (h3 : a.testBit 3 = true) (h4 : a.testBit 4 = true) : a = 31 := by
  apply Nat.eq_of_testBit_eq
  intro i
  match i with
  | 0 => exact h0
  | 1 => exact h1
  | 2 => exact h2
  | 3 => exact h3
  | 4 => exact h4
  | i + 5 =>
    have h_pow : 32 ≤ 2 ^ (i + 5) := by
      have : 2 ^ 5 ≤ 2 ^ (i + 5) := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    rw [Nat.testBit_lt_two_pow (by omega), Nat.testBit_lt_two_pow (by omega)]

/-- Soundness 2: Any active well-formed SWAR outlet preserves `MatchesCartState` under `narrowSWAR`. -/
theorem matchesCartState_narrowSWAR_of_outletActive (deg : Nat) (cartDeg : Nat → Nat) (st : Nat) (po : FastPosOut)
    (h_deg : deg ≤ 11)
    (h_valid : validFastPosOut deg po = true)
    (h_match : MatchesCartState deg cartDeg st)
    (h_active : OutletActive deg cartDeg po = true) :
    MatchesCartState deg cartDeg (narrowSWAR st po) := by
  apply matchesCartState_narrowSWAR deg cartDeg st po h_match
  intro p hp1 hp2
  dsimp [validFastPosOut] at h_valid
  simp only [Bool.and_eq_true, beq_iff_eq] at h_valid
  rcases h_valid with ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, _⟩, h_keep_all⟩, _⟩
  have hp60 : p < 60 := by omega
  have hb6 : degBitIdx (cartDeg p) < 6 := degBitIdx_lt_6 _
  have h_tb : (po.keep &&& all63Nat).testBit (p * 6 + degBitIdx (cartDeg p)) =
      (all31Nat ^^^ (po.forbid &&& all31Nat)).testBit (p * 6 + degBitIdx (cartDeg p)) := by
    rw [h_keep_all]
  rw [Nat.testBit_and, testBit_all63Nat_of_lt (by omega), Bool.and_true,
      ← testBit_getLaneNat po.keep p hb6,
      Nat.testBit_xor, Nat.testBit_and, testBit_all31Nat_of_lt_360 p hp60 hb6,
      testBit_31_degBitIdx, Bool.true_xor, Bool.and_true,
      ← testBit_getLaneNat po.forbid p hb6] at h_tb
  have hp_range : p ∈ List.range' 1 (5 * deg) := List.mem_range'.mpr ⟨p - 1, by omega, by omega⟩
  have h_not_forbid := List.all_eq_true.mp h_active p hp_range
  rw [h_tb]
  exact h_not_forbid

/-- Soundness 3: Any active well-formed SWAR outlet satisfies `outletPermittedSWAR st po = true`. -/
theorem outletPermittedSWAR_of_outletActive (deg : Nat) (cartDeg : Nat → Nat) (st : Nat) (po : FastPosOut)
    (h_deg : deg ≤ 11)
    (h_valid : validFastPosOut deg po = true)
    (h_match : MatchesCartState deg cartDeg st)
    (h_active : OutletActive deg cartDeg po = true) :
    outletPermittedSWAR st po = true := by
  have h_valid_orig := h_valid
  dsimp [validFastPosOut] at h_valid
  simp only [Bool.and_eq_true, beq_iff_eq] at h_valid
  rcases h_valid with ⟨⟨⟨⟨⟨⟨h_mask_eq, h_add31⟩, h_high_mask⟩, h_high_low⟩, h_high_up⟩, h_keep_all⟩, h_add_shifts⟩
  have h_mask31 : (po.mask &&& all31Nat) = po.mask := by
    rw [h_mask_eq, Nat.and_assoc, h_add31]
  dsimp [outletPermittedSWAR]
  rw [Nat.beq_eq]
  apply Nat.eq_of_testBit_eq
  intro k
  change (((st &&& po.mask) + po.add) &&& po.high).testBit k = po.high.testBit k
  rw [Nat.testBit_and]
  cases h_hk : po.high.testBit k with
  | false => simp
  | true =>
    rw [Bool.and_true]
    have h_hk_mask : (po.high &&& (all63Nat ^^^ all31Nat)).testBit k = true := by
      rw [h_high_mask, h_hk]
    rw [Nat.testBit_and, Nat.testBit_xor] at h_hk_mask
    have hk_lt360 : k < 360 := by
      by_cases hk : k < 360
      · exact hk
      · have h_ge360 : 360 ≤ k := by omega
        rw [testBit_all63Nat_of_ge_360 h_ge360, testBit_all31Nat_of_ge_360 h_ge360] at h_hk_mask
        simp at h_hk_mask
    let p := k / 6
    let i := k % 6
    have hp60 : p < 60 := by omega
    have hi6 : i < 6 := by omega
    have hk_eq : k = p * 6 + i := by omega
    have hi5 : i = 5 := by
      rw [hk_eq, testBit_all63Nat_of_lt (by omega), testBit_all31Nat_of_lt_360 p hp60 hi6] at h_hk_mask
      by_cases hi_lt5 : i < 5
      · rw [testBit_31_of_lt_5 hi_lt5] at h_hk_mask
        simp at h_hk_mask
      · omega
    have hp1 : 1 ≤ p := by
      by_cases hp0 : p = 0
      · have hk6 : k < 6 := by omega
        have h_tb0 : (po.high &&& 63).testBit k = false := by rw [h_high_low, Nat.zero_testBit]
        rw [Nat.testBit_and, h_hk, testBit_63_of_lt_6 hk6] at h_tb0
        contradiction
      · omega
    have hp2 : p ≤ 5 * deg := by
      by_cases hp_le : p ≤ 5 * deg
      · exact hp_le
      · have h_sh : (5 * deg + 1) * 6 ≤ k := by omega
        have h_tb_up : (po.high >>> ((5 * deg + 1) * 6)).testBit (k - (5 * deg + 1) * 6) = false := by
          rw [h_high_up, Nat.zero_testBit]
        rw [Nat.testBit_shiftRight, Nat.add_sub_of_le h_sh, h_hk] at h_tb_up
        contradiction
    have h_hk5 : po.high.testBit (p * 6 + 5) = true := by rw [← hi5, ← hk_eq, h_hk]
    have h_add_bit : ∀ b < 5, (getLaneNat po.add p).testBit b = true := by
      intro b hb
      rw [testBit_getLaneNat po.add p (by omega), h_add_shifts]
      simp only [Nat.testBit_or, Nat.testBit_shiftRight]
      match b with
      | 0 =>
        have : 5 + (p * 6 + 0) = p * 6 + 5 := by omega
        rw [this, h_hk5]; simp
      | 1 =>
        have : 4 + (p * 6 + 1) = p * 6 + 5 := by omega
        rw [this, h_hk5]; simp
      | 2 =>
        have : 3 + (p * 6 + 2) = p * 6 + 5 := by omega
        rw [this, h_hk5]; simp
      | 3 =>
        have : 2 + (p * 6 + 3) = p * 6 + 5 := by omega
        rw [this, h_hk5]; simp
      | 4 =>
        have : 1 + (p * 6 + 4) = p * 6 + 5 := by omega
        rw [this, h_hk5]; simp
    have h_Y_le : ∀ q, getLaneNat po.add q ≤ 31 :=
      getLaneNat_le_31_of_and_all31Nat po.add h_add31
    have h_add31_p : getLaneNat po.add p = 31 :=
      eq_31_of_le_31_of_testBits (h_Y_le p)
        (h_add_bit 0 (by omega)) (h_add_bit 1 (by omega)) (h_add_bit 2 (by omega))
        (h_add_bit 3 (by omega)) (h_add_bit 4 (by omega))
    have h_X_le : ∀ q, getLaneNat (st &&& po.mask) q ≤ 31 := by
      intro q
      have h_sub : ((st &&& po.mask) &&& all31Nat) = (st &&& po.mask) := by
        rw [Nat.and_assoc, h_mask31]
      exact getLaneNat_le_31_of_and_all31Nat (st &&& po.mask) h_sub q
    rw [hk_eq, hi5, ← testBit_getLaneNat _ p (by omega),
        getLaneNat_add_of_le_31 (st &&& po.mask) po.add h_X_le h_Y_le p,
        getLaneNat_and, h_mask_eq, getLaneNat_and, h_add31_p]
    have h_m_le : (getLaneNat st p &&& (getLaneNat po.keep p &&& 31)) ≤ 31 :=
      Nat.le_trans Nat.and_le_right Nat.and_le_right
    have h_keep_bit : (getLaneNat po.keep p).testBit (degBitIdx (cartDeg p)) = true := by
      have h_m_narrow := matchesCartState_narrowSWAR_of_outletActive deg cartDeg st po h_deg
        h_valid_orig h_match h_active p hp1 hp2
      rw [testBit_getLaneNat_narrowSWAR st po p (degBitIdx_lt_6 _)] at h_m_narrow
      simpa using (Bool.and_eq_true _ _).mp h_m_narrow |>.2
    have h_and_bit : (getLaneNat st p &&& (getLaneNat po.keep p &&& 31)).testBit (degBitIdx (cartDeg p)) = true := by
      rw [Nat.testBit_and, Nat.testBit_and, h_match p hp1 hp2, h_keep_bit, testBit_31_degBitIdx]; rfl
    exact testBit_add_31_five_of_testBit_lt_5 h_m_le (degBitIdx_lt_5 _) h_and_bit

/-!
### Stage J.2: Inductive Soundness of `filterNegAPS`, `filterRemAPS`, `checkBoundRec`, and `verifyHubcapMembersRec`
-/

/-- Signed value (`+1` or `-1`) of a `FastPosOut` outlet. -/
def outletVal (po : FastPosOut) : Int :=
  if po.isPos then 1 else -1

/-- Sum of `outletVal po` over all outlets in `l` that are active on `cartDeg` at hub degree `deg`. -/
def activeOutletSum (deg : Nat) (cartDeg : Nat → Nat) : List FastPosOut → Int
  | [] => 0
  | po :: rest =>
    (if OutletActive deg cartDeg po then outletVal po else 0) + activeOutletSum deg cartDeg rest

/-- Number of positive outlets (`po.isPos = true`) in `l`. -/
def countPos : List FastPosOut → Nat
  | [] => 0
  | po :: rest => (if po.isPos then 1 else 0) + countPos rest

theorem activeOutletSum_append (deg : Nat) (cartDeg : Nat → Nat) (l1 l2 : List FastPosOut) :
    activeOutletSum deg cartDeg (l1 ++ l2) =
      activeOutletSum deg cartDeg l1 + activeOutletSum deg cartDeg l2 := by
  induction l1 with
  | nil => simp [activeOutletSum]
  | cons po rest ih =>
    simp only [List.cons_append, activeOutletSum, ih]
    omega

theorem countPos_append (l1 l2 : List FastPosOut) :
    countPos (l1 ++ l2) = countPos l1 + countPos l2 := by
  induction l1 with
  | nil => simp [countPos]
  | cons po rest ih =>
    simp only [List.cons_append, countPos, ih]
    omega

theorem appendFastPosOut_eq_append (l1 l2 : List FastPosOut) :
    appendFastPosOut l1 l2 = l1 ++ l2 := by
  induction l1 with
  | nil => rfl
  | cons x rest ih =>
    change x :: appendFastPosOut rest l2 = x :: (rest ++ l2)
    rw [ih]

theorem revFastPosOut_loop_eq (l acc : List FastPosOut) :
    List.rec (motive := fun _ => List FastPosOut → List FastPosOut)
      (fun a => a) (fun x _ ih a => ih (x :: a)) l acc = l.reverse ++ acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons x rest ih =>
    change List.rec (motive := fun _ => List FastPosOut → List FastPosOut)
      (fun a => a) (fun x _ ih a => ih (x :: a)) rest (x :: acc) = (x :: rest).reverse ++ acc
    rw [ih (x :: acc), List.reverse_cons, List.append_assoc]
    rfl

theorem revFastPosOut_eq_reverse (l : List FastPosOut) :
    revFastPosOut l = l.reverse := by
  dsimp [revFastPosOut]
  rw [revFastPosOut_loop_eq l [], List.append_nil]

theorem activeOutletSum_reverse (deg : Nat) (cartDeg : Nat → Nat) (l : List FastPosOut) :
    activeOutletSum deg cartDeg l.reverse = activeOutletSum deg cartDeg l := by
  induction l with
  | nil => rfl
  | cons po rest ih =>
    rw [List.reverse_cons, activeOutletSum_append, ih]
    simp only [activeOutletSum]
    omega

theorem countPos_reverse (l : List FastPosOut) :
    countPos l.reverse = countPos l := by
  induction l with
  | nil => rfl
  | cons po rest ih =>
    rw [List.reverse_cons, countPos_append, ih]
    simp only [countPos]
    omega

theorem activeOutletSum_le_countPos (deg : Nat) (cartDeg : Nat → Nat) (l : List FastPosOut) :
    activeOutletSum deg cartDeg l ≤ (countPos l : Int) := by
  induction l with
  | nil => simp [activeOutletSum, countPos]
  | cons po rest ih =>
    simp only [activeOutletSum, countPos, outletVal]
    cases po.isPos <;> cases OutletActive deg cartDeg po <;> simp <;> omega

theorem activeOutletSum_le_zero_of_all_neg (deg : Nat) (cartDeg : Nat → Nat) (l : List FastPosOut)
    (h_neg : ∀ po ∈ l, po.isPos = false) :
    activeOutletSum deg cartDeg l ≤ 0 := by
  induction l with
  | nil => simp [activeOutletSum]
  | cons po rest ih =>
    have h_po : po.isPos = false := h_neg po List.mem_cons_self
    have h_rest : ∀ q ∈ rest, q.isPos = false := fun q hq => h_neg q (List.mem_cons_of_mem po hq)
    have ih_le := ih h_rest
    simp only [activeOutletSum, outletVal, h_po]
    cases OutletActive deg cartDeg po <;> simp <;> omega

noncomputable def filterNegStep (st : Nat) (l : List FastPosOut) (f0 : Nat) (acc0 : List FastPosOut) :
    Nat × List FastPosOut :=
  List.rec
    (motive := fun _ => Nat → List FastPosOut → Nat × List FastPosOut)
    (fun f acc => strictNat f fun f' => (f', acc))
    (fun po _ ih f acc =>
      Bool.rec
        (Bool.rec
          (ih f acc)
          (ih f (po :: acc))
          (outletPermittedSWAR st po))
        (ih (Bool.rec (Nat.sub f 1) (Nat.add f 1) po.isPos) acc)
        (outletForcedSWAR st po))
    l f0 acc0

theorem filterNegAPS_eq_step (st : Nat) (negBefore : List FastPosOut) (f0 : Nat) :
    filterNegAPS st negBefore f0 = filterNegStep st negBefore f0 [] := rfl

theorem filterNegStep_nil (st : Nat) (f : Nat) (acc : List FastPosOut) :
    filterNegStep st [] f acc = (f, acc) := by
  change strictNat f (fun f' => (f', acc)) = (f, acc)
  rw [strictNat_eq]

theorem filterNegStep_cons (st : Nat) (po : FastPosOut) (rest : List FastPosOut) (f : Nat) (acc : List FastPosOut) :
    filterNegStep st (po :: rest) f acc =
      @Bool.rec (fun _ => Nat × List FastPosOut)
        (@Bool.rec (fun _ => Nat × List FastPosOut)
          (filterNegStep st rest f acc)
          (filterNegStep st rest f (po :: acc))
          (outletPermittedSWAR st po))
        (filterNegStep st rest (@Bool.rec (fun _ => Nat) (Nat.sub f 1) (Nat.add f 1) po.isPos) acc)
        (outletForcedSWAR st po) := rfl

theorem filterNegStep_sound (deg : Nat) (cartDeg : Nat → Nat) (st : Nat)
    (h_deg : deg ≤ 11) (h_match : MatchesCartState deg cartDeg st)
    (l : List FastPosOut) :
    ∀ (f : Nat) (acc : List FastPosOut),
      (∀ po ∈ l, validFastPosOut deg po = true ∧ po.isPos = false) →
      (∀ po ∈ acc, validFastPosOut deg po = true ∧ po.isPos = false) →
      let res := filterNegStep st l f acc
      (∀ po ∈ res.2, validFastPosOut deg po = true ∧ po.isPos = false) ∧
      (f : Int) + activeOutletSum deg cartDeg acc + activeOutletSum deg cartDeg l ≤
        (res.1 : Int) + activeOutletSum deg cartDeg res.2 := by
  induction l with
  | nil =>
    intro f acc _ h_acc
    dsimp only
    rw [filterNegStep_nil]
    simp only [activeOutletSum]
    exact ⟨h_acc, by omega⟩
  | cons po rest ih =>
    intro f acc h_l h_acc
    have h_po := h_l po List.mem_cons_self
    have h_rest : ∀ q ∈ rest, validFastPosOut deg q = true ∧ q.isPos = false :=
      fun q hq => h_l q (List.mem_cons_of_mem po hq)
    dsimp only
    rw [filterNegStep_cons]
    cases h_forced : outletForcedSWAR st po with
    | true =>
      dsimp only
      have h_act := outletActive_of_outletForcedSWAR deg cartDeg st po h_match h_forced
      rw [h_po.2]
      dsimp only
      have h_ih := ih (Nat.sub f 1) acc h_rest h_acc
      refine ⟨h_ih.1, ?_⟩
      have h_ih2 := h_ih.2
      have h_f_sub : (f : Int) - 1 ≤ (Nat.sub f 1 : Int) := by simp [Nat.sub_eq]; omega
      have h_sum_cons : activeOutletSum deg cartDeg (po :: rest) = -1 + activeOutletSum deg cartDeg rest := by
        simp [activeOutletSum, outletVal, h_act, h_po.2]
      omega
    | false =>
      dsimp only
      cases h_perm : outletPermittedSWAR st po with
      | true =>
        dsimp only
        have h_acc' : ∀ q ∈ po :: acc, validFastPosOut deg q = true ∧ q.isPos = false := by
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq_mem
          · exact h_po
          · exact h_acc q hq_mem
        have h_ih := ih f (po :: acc) h_rest h_acc'
        refine ⟨h_ih.1, ?_⟩
        simp only [activeOutletSum] at h_ih ⊢
        have := h_ih.2
        omega
      | false =>
        dsimp only
        have h_inact : OutletActive deg cartDeg po = false := by
          cases h_act : OutletActive deg cartDeg po with
          | false => rfl
          | true =>
            have := outletPermittedSWAR_of_outletActive deg cartDeg st po h_deg h_po.1 h_match h_act
            rw [this] at h_perm; contradiction
        have h_ih := ih f acc h_rest h_acc
        refine ⟨h_ih.1, ?_⟩
        simp only [activeOutletSum, h_inact, Bool.false_eq_true, ↓reduceIte]
        have := h_ih.2
        omega

theorem filterNegAPS_sound (deg : Nat) (cartDeg : Nat → Nat) (st : Nat)
    (h_deg : deg ≤ 11) (h_match : MatchesCartState deg cartDeg st)
    (negBefore : List FastPosOut) (f0 : Nat)
    (h_neg : ∀ po ∈ negBefore, validFastPosOut deg po = true ∧ po.isPos = false) :
    let res := filterNegAPS st negBefore f0
    (∀ po ∈ res.2, validFastPosOut deg po = true ∧ po.isPos = false) ∧
    (f0 : Int) + activeOutletSum deg cartDeg negBefore ≤
      (res.1 : Int) + activeOutletSum deg cartDeg res.2 := by
  rw [filterNegAPS_eq_step]
  have h := filterNegStep_sound deg cartDeg st h_deg h_match negBefore f0 [] h_neg (by intro _ h; contradiction)
  simpa [activeOutletSum] using h

noncomputable def filterRemStep (st : Nat) (l : List FastPosOut) (f0 a0 : Nat) (acc0 : List FastPosOut) :
    Nat × Nat × List FastPosOut :=
  List.rec
    (motive := fun _ => Nat → Nat → List FastPosOut → Nat × Nat × List FastPosOut)
    (fun f a acc =>
      strictNat f fun f' =>
      strictNat a fun a' =>
      (f', a', revFastPosOut acc))
    (fun po _ ih f a acc =>
      Bool.rec
        (Bool.rec
          (ih f a acc)
          (Bool.rec
            (ih f a (po :: acc))
            (ih f (Nat.add a 1) (po :: acc))
            po.isPos)
          (outletPermittedSWAR st po))
        (ih (Bool.rec (Nat.sub f 1) (Nat.add f 1) po.isPos) a acc)
        (outletForcedSWAR st po))
    l f0 a0 acc0

theorem filterRemAPS_eq_step (st : Nat) (rem : List FastPosOut) (f0 : Nat) :
    filterRemAPS st rem f0 = filterRemStep st rem f0 0 [] := rfl

theorem filterRemStep_nil (st : Nat) (f a : Nat) (acc : List FastPosOut) :
    filterRemStep st [] f a acc = (f, a, revFastPosOut acc) := by
  change (strictNat f fun f' => strictNat a fun a' => (f', a', revFastPosOut acc)) = (f, a, revFastPosOut acc)
  simp only [strictNat_eq]

theorem filterRemStep_cons (st : Nat) (po : FastPosOut) (rest : List FastPosOut) (f a : Nat) (acc : List FastPosOut) :
    filterRemStep st (po :: rest) f a acc =
      @Bool.rec (fun _ => Nat × Nat × List FastPosOut)
        (@Bool.rec (fun _ => Nat × Nat × List FastPosOut)
          (filterRemStep st rest f a acc)
          (@Bool.rec (fun _ => Nat × Nat × List FastPosOut)
            (filterRemStep st rest f a (po :: acc))
            (filterRemStep st rest f (Nat.add a 1) (po :: acc))
            po.isPos)
          (outletPermittedSWAR st po))
        (filterRemStep st rest (@Bool.rec (fun _ => Nat) (Nat.sub f 1) (Nat.add f 1) po.isPos) a acc)
        (outletForcedSWAR st po) := rfl

theorem filterRemStep_sound (deg : Nat) (cartDeg : Nat → Nat) (st : Nat)
    (h_deg : deg ≤ 11) (h_match : MatchesCartState deg cartDeg st)
    (l : List FastPosOut) :
    ∀ (f a : Nat) (acc : List FastPosOut),
      a = countPos acc →
      (∀ po ∈ l, validFastPosOut deg po = true) →
      (∀ po ∈ acc, validFastPosOut deg po = true) →
      let res := filterRemStep st l f a acc
      (∀ po ∈ res.2.2, validFastPosOut deg po = true) ∧
      res.2.1 = countPos res.2.2 ∧
      (f : Int) + activeOutletSum deg cartDeg acc + activeOutletSum deg cartDeg l ≤
        (res.1 : Int) + activeOutletSum deg cartDeg res.2.2 := by
  induction l with
  | nil =>
    intro f a acc ha _ h_acc
    dsimp only
    rw [filterRemStep_nil, revFastPosOut_eq_reverse, countPos_reverse, activeOutletSum_reverse]
    refine ⟨?_, ha, by simp [activeOutletSum]⟩
    intro po hpo
    exact h_acc po (List.mem_reverse.mp hpo)
  | cons po rest ih =>
    intro f a acc ha h_l h_acc
    have h_po := h_l po List.mem_cons_self
    have h_rest : ∀ q ∈ rest, validFastPosOut deg q = true :=
      fun q hq => h_l q (List.mem_cons_of_mem po hq)
    dsimp only
    rw [filterRemStep_cons]
    cases h_forced : outletForcedSWAR st po with
    | true =>
      dsimp only
      have h_act := outletActive_of_outletForcedSWAR deg cartDeg st po h_match h_forced
      cases h_pos : po.isPos with
      | true =>
        dsimp only
        have h_ih := ih (Nat.add f 1) a acc ha h_rest h_acc
        refine ⟨h_ih.1, h_ih.2.1, ?_⟩
        have h_ih2 := h_ih.2.2
        simp only [Nat.add_eq, activeOutletSum, outletVal, h_act, h_pos, ↓reduceIte] at h_ih2 ⊢
        omega
      | false =>
        dsimp only
        have h_ih := ih (Nat.sub f 1) a acc ha h_rest h_acc
        refine ⟨h_ih.1, h_ih.2.1, ?_⟩
        have h_ih2 := h_ih.2.2
        simp only [Nat.sub_eq, activeOutletSum, outletVal, h_act, h_pos, Bool.false_eq_true, ↓reduceIte] at h_ih2 ⊢
        omega
    | false =>
      dsimp only
      cases h_perm : outletPermittedSWAR st po with
      | true =>
        dsimp only
        have h_acc' : ∀ q ∈ po :: acc, validFastPosOut deg q = true := by
          intro q hq
          rcases List.mem_cons.mp hq with rfl | hq_mem
          · exact h_po
          · exact h_acc q hq_mem
        cases h_pos : po.isPos with
        | true =>
          dsimp only
          have ha' : Nat.add a 1 = countPos (po :: acc) := by
            simp [countPos, h_pos, ha]; omega
          have h_ih := ih f (Nat.add a 1) (po :: acc) ha' h_rest h_acc'
          refine ⟨h_ih.1, h_ih.2.1, ?_⟩
          have h_ih2 := h_ih.2.2
          simp only [activeOutletSum] at h_ih2 ⊢
          omega
        | false =>
          dsimp only
          have ha' : a = countPos (po :: acc) := by
            simp [countPos, h_pos, ha]
          have h_ih := ih f a (po :: acc) ha' h_rest h_acc'
          refine ⟨h_ih.1, h_ih.2.1, ?_⟩
          have h_ih2 := h_ih.2.2
          simp only [activeOutletSum] at h_ih2 ⊢
          omega
      | false =>
        dsimp only
        have h_inact : OutletActive deg cartDeg po = false := by
          cases h_act : OutletActive deg cartDeg po with
          | false => rfl
          | true =>
            have := outletPermittedSWAR_of_outletActive deg cartDeg st po h_deg h_po h_match h_act
            rw [this] at h_perm; contradiction
        have h_ih := ih f a acc ha h_rest h_acc
        refine ⟨h_ih.1, h_ih.2.1, ?_⟩
        have h_ih2 := h_ih.2.2
        simp only [activeOutletSum, h_inact, Bool.false_eq_true, ↓reduceIte] at h_ih2 ⊢
        omega

theorem filterRemAPS_sound (deg : Nat) (cartDeg : Nat → Nat) (st : Nat)
    (h_deg : deg ≤ 11) (h_match : MatchesCartState deg cartDeg st)
    (rem : List FastPosOut) (f0 : Nat)
    (h_rem : ∀ po ∈ rem, validFastPosOut deg po = true) :
    let res := filterRemAPS st rem f0
    (∀ po ∈ res.2.2, validFastPosOut deg po = true) ∧
    res.2.1 = countPos res.2.2 ∧
    (f0 : Int) + activeOutletSum deg cartDeg rem ≤
      (res.1 : Int) + activeOutletSum deg cartDeg res.2.2 := by
  rw [filterRemAPS_eq_step]
  have h := filterRemStep_sound deg cartDeg st h_deg h_match rem f0 0 [] rfl h_rem (by intro _ h; contradiction)
  simpa [activeOutletSum] using h

theorem noExcludedForcedRec_nil (st : Nat) : noExcludedForcedRec st [] = true := rfl

theorem noExcludedForcedRec_cons (st : Nat) (ex : FastPosOut) (rest : List FastPosOut) :
    noExcludedForcedRec st (ex :: rest) =
      @Bool.rec (fun _ => Bool) (noExcludedForcedRec st rest) false (outletForcedSWAR st ex) := rfl

theorem noExcludedForcedRec_eq_true (deg : Nat) (cartDeg : Nat → Nat) (st : Nat)
    (h_match : MatchesCartState deg cartDeg st)
    (excluded : List FastPosOut)
    (h_excl : ∀ ex ∈ excluded, OutletActive deg cartDeg ex = false) :
    noExcludedForcedRec st excluded = true := by
  induction excluded with
  | nil => rfl
  | cons ex rest ih =>
    rw [noExcludedForcedRec_cons]
    cases h_forced : outletForcedSWAR st ex with
    | true =>
      have h_act := outletActive_of_outletForcedSWAR deg cartDeg st ex h_match h_forced
      have h_inact := h_excl ex List.mem_cons_self
      rw [h_act] at h_inact; contradiction
    | false =>
      dsimp only
      exact ih (fun q hq => h_excl q (List.mem_cons_of_mem ex hq))

theorem checkBoundLoopRec_nil
    (cb : Nat → Nat → List FastPosOut → List FastPosOut → List FastPosOut → Nat → HintStream → Bool × HintStream)
    (st forcedch maxch : Nat) (allowed0 : Nat) (neg0 excl0 : List FastPosOut) (hs0 : HintStream) :
    checkBoundLoopRec cb st forcedch maxch [] allowed0 neg0 excl0 hs0 = (false, hs0) := rfl

theorem checkBoundLoopRec_cons_eq
    (cb : Nat → Nat → List FastPosOut → List FastPosOut → List FastPosOut → Nat → HintStream → Bool × HintStream)
    (st forcedch maxch : Nat) (po : FastPosOut) (subRem : List FastPosOut)
    (allowedch : Nat) (negBefore curExcluded : List FastPosOut) (hs : HintStream) :
    checkBoundLoopRec cb st forcedch maxch (po :: subRem) allowedch negBefore curExcluded hs =
      @Bool.rec (fun _ => Bool × HintStream)
        (checkBoundLoopRec cb st forcedch maxch subRem allowedch (po :: negBefore) curExcluded hs)
        (strictNat (narrowSWAR st po) fun st_next =>
         strictNat (Nat.add forcedch 1) fun forced_next =>
         let (okSub, hs') :=
           @Bool.rec (fun _ => Bool × HintStream)
             (true, hs)
             (cb st_next forced_next negBefore subRem curExcluded maxch hs)
             (noExcludedForcedRec st_next curExcluded)
         @Bool.rec (fun _ => Bool × HintStream)
           (false, hs')
           (strictNat (Nat.sub allowedch 1) fun allowedch' =>
            @Bool.rec (fun _ => Bool × HintStream)
              (checkBoundLoopRec cb st forcedch maxch subRem allowedch' negBefore (po :: curExcluded) hs')
              (true, hs')
              (Nat.ble (Nat.add allowedch' forcedch) maxch))
           okSub)
        po.isPos := rfl

theorem checkBoundLoopRec_sound (deg : Nat) (cartDeg : Nat → Nat) (h_deg : deg ≤ 11)
    (cb : Nat → Nat → List FastPosOut → List FastPosOut → List FastPosOut → Nat → HintStream → Bool × HintStream)
    (h_cb : ∀ (st' forcedIn' : Nat) (negBefore' rem' excluded' : List FastPosOut) (maxch' : Nat) (hs' : HintStream),
      MatchesCartState deg cartDeg st' →
      (∀ po ∈ negBefore', validFastPosOut deg po = true ∧ po.isPos = false) →
      (∀ po ∈ rem', validFastPosOut deg po = true) →
      (∀ ex ∈ excluded', OutletActive deg cartDeg ex = false) →
      (cb st' forcedIn' negBefore' rem' excluded' maxch' hs').1 = true →
      (∃ st_red hs_red, MatchesCartState deg cartDeg st_red ∧ (reduceAxleRec deg 64 [st_red] hs_red).1 = true) ∨
      (forcedIn' : Int) + activeOutletSum deg cartDeg negBefore' + activeOutletSum deg cartDeg rem' ≤ (maxch' : Int))
    (st forcedch maxch : Nat) (h_match : MatchesCartState deg cartDeg st)
    (rem : List FastPosOut) :
    ∀ (allowedch : Nat) (negBefore curExcluded : List FastPosOut) (hs : HintStream),
      allowedch = countPos rem →
      (∀ po ∈ negBefore, validFastPosOut deg po = true ∧ po.isPos = false) →
      (∀ po ∈ rem, validFastPosOut deg po = true) →
      (∀ ex ∈ curExcluded, OutletActive deg cartDeg ex = false) →
      (checkBoundLoopRec cb st forcedch maxch rem allowedch negBefore curExcluded hs).1 = true →
      (∃ st_red hs_red, MatchesCartState deg cartDeg st_red ∧ (reduceAxleRec deg 64 [st_red] hs_red).1 = true) ∨
      (forcedch : Int) + activeOutletSum deg cartDeg negBefore + activeOutletSum deg cartDeg rem ≤ (maxch : Int) := by
  induction rem with
  | nil =>
    intro allowedch negBefore curExcluded hs _ _ _ _ h_ok
    rw [checkBoundLoopRec_nil] at h_ok
    contradiction
  | cons po subRem ih =>
    intro allowedch negBefore curExcluded hs h_all h_neg h_rem h_excl h_ok
    have h_po := h_rem po List.mem_cons_self
    have h_sub : ∀ q ∈ subRem, validFastPosOut deg q = true :=
      fun q hq => h_rem q (List.mem_cons_of_mem po hq)
    rw [checkBoundLoopRec_cons_eq] at h_ok
    simp only [strictNat_eq] at h_ok
    cases h_pos : po.isPos with
    | false =>
      rw [h_pos] at h_ok
      dsimp only at h_ok
      have h_all' : allowedch = countPos subRem := by
        simpa [countPos, h_pos] using h_all
      have h_neg' : ∀ q ∈ po :: negBefore, validFastPosOut deg q = true ∧ q.isPos = false := by
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq_mem
        · exact ⟨h_po, h_pos⟩
        · exact h_neg q hq_mem
      rcases ih allowedch (po :: negBefore) curExcluded hs h_all' h_neg' h_sub h_excl h_ok with h_red | h_bound
      · exact Or.inl h_red
      · right
        simp only [activeOutletSum] at h_bound ⊢
        omega
    | true =>
      rw [h_pos] at h_ok
      dsimp only at h_ok
      cases h_act : OutletActive deg cartDeg po with
      | true =>
        have h_match_next := matchesCartState_narrowSWAR_of_outletActive deg cartDeg st po h_deg h_po h_match h_act
        have h_no_excl := noExcludedForcedRec_eq_true deg cartDeg (narrowSWAR st po) h_match_next curExcluded h_excl
        rw [h_no_excl] at h_ok
        dsimp only at h_ok
        cases h_cb_ok : (cb (narrowSWAR st po) (Nat.add forcedch 1) negBefore subRem curExcluded maxch hs).fst with
        | false =>
          rw [h_cb_ok] at h_ok; dsimp only at h_ok; contradiction
        | true =>
          rcases h_cb (narrowSWAR st po) (Nat.add forcedch 1) negBefore subRem curExcluded maxch hs
            h_match_next h_neg h_sub h_excl h_cb_ok with h_red | h_bound
          · exact Or.inl h_red
          · right
            simp only [Nat.add_eq, activeOutletSum, outletVal, h_act, h_pos, ↓reduceIte] at h_bound ⊢
            omega
      | false =>
        let resSub :=
          @Bool.rec (fun _ => Bool × HintStream)
            (true, hs)
            (cb (narrowSWAR st po) (Nat.add forcedch 1) negBefore subRem curExcluded maxch hs)
            (noExcludedForcedRec (narrowSWAR st po) curExcluded)
        change (@Bool.rec (fun _ => Bool × HintStream)
          (false, resSub.2)
          (@Bool.rec (fun _ => Bool × HintStream)
            (checkBoundLoopRec cb st forcedch maxch subRem (Nat.sub allowedch 1) negBefore (po :: curExcluded) resSub.2)
            (true, resSub.2)
            (Nat.ble (Nat.add (Nat.sub allowedch 1) forcedch) maxch))
          resSub.1).1 = true at h_ok
        cases h_okSub : resSub.1 with
        | false =>
          rw [h_okSub] at h_ok; dsimp only at h_ok; contradiction
        | true =>
          rw [h_okSub] at h_ok; dsimp only at h_ok
          have h_all' : Nat.sub allowedch 1 = countPos subRem := by
            have : allowedch = 1 + countPos subRem := by simpa [countPos, h_pos] using h_all
            simp only [Nat.sub_eq]
            omega
          cases h_ble : Nat.ble (Nat.add (Nat.sub allowedch 1) forcedch) maxch with
          | true =>
            right
            have h_le : (Nat.sub allowedch 1) + forcedch ≤ maxch := Nat.le_of_ble_eq_true h_ble
            have h_neg_le : activeOutletSum deg cartDeg negBefore ≤ 0 :=
              activeOutletSum_le_zero_of_all_neg deg cartDeg negBefore (fun q hq => (h_neg q hq).2)
            have h_sub_le : activeOutletSum deg cartDeg subRem ≤ (countPos subRem : Int) :=
              activeOutletSum_le_countPos deg cartDeg subRem
            simp only [activeOutletSum, h_act, Bool.false_eq_true, ↓reduceIte]
            omega
          | false =>
            rw [h_ble] at h_ok; dsimp only at h_ok
            have h_excl' : ∀ ex ∈ po :: curExcluded, OutletActive deg cartDeg ex = false := by
              intro ex hex
              rcases List.mem_cons.mp hex with rfl | hex_mem
              · exact h_act
              · exact h_excl ex hex_mem
            rcases ih (Nat.sub allowedch 1) negBefore (po :: curExcluded) resSub.2 h_all' h_neg h_sub h_excl' h_ok with h_red | h_bound
            · exact Or.inl h_red
            · right
              simp only [activeOutletSum, h_act, Bool.false_eq_true, ↓reduceIte]
              omega

theorem checkBoundRec_zero (deg st forcedIn : Nat) (negBefore rem excluded : List FastPosOut)
    (maxch : Nat) (hs : HintStream) :
    checkBoundRec deg 0 st forcedIn negBefore rem excluded maxch hs = (false, hs) := rfl

theorem checkBoundRec_succ_eq (deg fuel st forcedIn : Nat) (negBefore rem excluded : List FastPosOut)
    (maxch : Nat) (hs : HintStream) :
    checkBoundRec deg (fuel + 1) st forcedIn negBefore rem excluded maxch hs =
      (let (forced1, nextNegBefore) := filterNegAPS st negBefore forcedIn
       let (forcedch, allowedch, nextRem) := filterRemAPS st rem forced1
       @Bool.rec (fun _ => Bool × HintStream)
         (@Bool.rec (fun _ => Bool × HintStream)
           (checkBoundLoopRec (checkBoundRec deg fuel) st forcedch maxch nextRem allowedch nextNegBefore excluded hs)
           (reduceAxleRec deg 64 [st] hs)
           (Nat.ble (Nat.add maxch 1) forcedch))
         (true, hs)
         (Nat.ble (Nat.add forcedch allowedch) maxch)) := rfl

/-- Fundamental Inductive Soundness of `checkBoundRec`:
    whenever `(checkBoundRec deg fuel st forcedIn negBefore rem excluded maxch hs).1 = true`
    on a state `st` matching `cartDeg` (with `deg ≤ 11`), either `reduceAxleRec` succeeds on a
    refinement `st_red` matching `cartDeg`, or the active outlet sum plus `forcedIn` is at most `maxch`. -/
theorem checkBoundRec_sound (deg : Nat) (cartDeg : Nat → Nat) (h_deg : deg ≤ 11) (fuel : Nat) :
    ∀ (st forcedIn : Nat) (negBefore rem excluded : List FastPosOut) (maxch : Nat) (hs : HintStream),
      MatchesCartState deg cartDeg st →
      (∀ po ∈ negBefore, validFastPosOut deg po = true ∧ po.isPos = false) →
      (∀ po ∈ rem, validFastPosOut deg po = true) →
      (∀ ex ∈ excluded, OutletActive deg cartDeg ex = false) →
      (checkBoundRec deg fuel st forcedIn negBefore rem excluded maxch hs).1 = true →
      (∃ st_red hs_red, MatchesCartState deg cartDeg st_red ∧ (reduceAxleRec deg 64 [st_red] hs_red).1 = true) ∨
      (forcedIn : Int) + activeOutletSum deg cartDeg negBefore + activeOutletSum deg cartDeg rem ≤ (maxch : Int) := by
  induction fuel with
  | zero =>
    intro st forcedIn negBefore rem excluded maxch hs _ _ _ _ h_ok
    rw [checkBoundRec_zero] at h_ok
    contradiction
  | succ fuel ih =>
    intro st forcedIn negBefore rem excluded maxch hs h_match h_neg h_rem h_excl h_ok
    rw [checkBoundRec_succ_eq] at h_ok
    have h_fneg := filterNegAPS_sound deg cartDeg st h_deg h_match negBefore forcedIn h_neg
    let forced1 := (filterNegAPS st negBefore forcedIn).1
    let nextNegBefore := (filterNegAPS st negBefore forcedIn).2
    have h_frem := filterRemAPS_sound deg cartDeg st h_deg h_match rem forced1 h_rem
    let forcedch := (filterRemAPS st rem forced1).1
    let allowedch := (filterRemAPS st rem forced1).2.1
    let nextRem := (filterRemAPS st rem forced1).2.2
    change (@Bool.rec (fun _ => Bool × HintStream)
      (@Bool.rec (fun _ => Bool × HintStream)
        (checkBoundLoopRec (checkBoundRec deg fuel) st forcedch maxch nextRem allowedch nextNegBefore excluded hs)
        (reduceAxleRec deg 64 [st] hs)
        (Nat.ble (Nat.add maxch 1) forcedch))
      (true, hs)
      (Nat.ble (Nat.add forcedch allowedch) maxch)).1 = true at h_ok
    cases h_ble1 : Nat.ble (Nat.add forcedch allowedch) maxch with
    | true =>
      right
      have h_le : forcedch + allowedch ≤ maxch := Nat.le_of_ble_eq_true h_ble1
      have h_neg_le : activeOutletSum deg cartDeg nextNegBefore ≤ 0 :=
        activeOutletSum_le_zero_of_all_neg deg cartDeg nextNegBefore (fun q hq => (h_fneg.1 q hq).2)
      have h_rem_le : activeOutletSum deg cartDeg nextRem ≤ (countPos nextRem : Int) :=
        activeOutletSum_le_countPos deg cartDeg nextRem
      have h_all_eq : allowedch = countPos nextRem := h_frem.2.1
      have h1 : (forcedIn : Int) + activeOutletSum deg cartDeg negBefore ≤
          (forced1 : Int) + activeOutletSum deg cartDeg nextNegBefore := h_fneg.2
      have h2 : (forced1 : Int) + activeOutletSum deg cartDeg rem ≤
          (forcedch : Int) + activeOutletSum deg cartDeg nextRem := h_frem.2.2
      omega
    | false =>
      rw [h_ble1] at h_ok; dsimp only at h_ok
      cases h_ble2 : Nat.ble (Nat.add maxch 1) forcedch with
      | true =>
        rw [h_ble2] at h_ok; dsimp only at h_ok
        exact Or.inl ⟨st, hs, h_match, h_ok⟩
      | false =>
        rw [h_ble2] at h_ok; dsimp only at h_ok
        rcases checkBoundLoopRec_sound deg cartDeg h_deg (checkBoundRec deg fuel) ih
          st forcedch maxch h_match nextRem allowedch nextNegBefore excluded hs
          h_frem.2.1 h_fneg.1 h_frem.1 h_excl h_ok with h_red | h_bound
        · exact Or.inl h_red
        · right
          have h1 : (forcedIn : Int) + activeOutletSum deg cartDeg negBefore ≤
              (forced1 : Int) + activeOutletSum deg cartDeg nextNegBefore := h_fneg.2
          have h2 : (forced1 : Int) + activeOutletSum deg cartDeg rem ≤
              (forcedch : Int) + activeOutletSum deg cartDeg nextRem := h_frem.2.2
          omega

theorem lookupListRec_mem_or_default {α : Type} (d : α) (l : List α) (idx : Nat) :
    lookupListRec d l idx = d ∨ lookupListRec d l idx ∈ l := by
  induction l generalizing idx with
  | nil => exact Or.inl rfl
  | cons x rest ih =>
    cases idx with
    | zero =>
      change x = d ∨ x ∈ x :: rest
      exact Or.inr List.mem_cons_self
    | succ k =>
      change lookupListRec d rest k = d ∨ lookupListRec d rest k ∈ x :: rest
      rcases ih k with h_def | h_mem
      · exact Or.inl h_def
      · exact Or.inr (List.mem_cons_of_mem x h_mem)

theorem validFastPosOut_lookupListRec (deg : Nat) (shiftedTable : List (List FastPosOut))
    (h_table : ∀ row ∈ shiftedTable, ∀ po ∈ row, validFastPosOut deg po = true)
    (idx : Nat) :
    ∀ po ∈ lookupListRec [] shiftedTable idx, validFastPosOut deg po = true := by
  rcases lookupListRec_mem_or_default [] shiftedTable idx with h_nil | h_mem
  · rw [h_nil]; intro _ h; contradiction
  · exact h_table _ h_mem

theorem verifyHubcapMembersRec_cons (deg st : Nat) (shiftedTable : List (List FastPosOut))
    (m : Nat × Nat × Int) (rest : List (Nat × Nat × Int)) (hs : HintStream) :
    verifyHubcapMembersRec deg st shiftedTable (m :: rest) hs =
      (let (x, y, v) := m
       let outsX := lookupListRec [] shiftedTable x
       let initRem :=
         @Bool.rec (fun _ => List FastPosOut)
           outsX
           (appendFastPosOut outsX (lookupListRec [] shiftedTable y))
           (!Nat.beq x y)
       let maxchNat := (v + 500).toNat
       strictNat maxchNat fun maxchStrict =>
       let (ok, hs') := checkBoundRec deg 20 st 500 [] initRem [] maxchStrict hs
       @Bool.rec (fun _ => Bool × HintStream) (false, hs') (verifyHubcapMembersRec deg st shiftedTable rest hs') ok) := rfl

/-- Soundness of `verifyHubcapMembersRec`:
    Whenever `(verifyHubcapMembersRec deg st shiftedTable members hs).1 = true` on a state `st`
    matching `cartDeg` (with `deg ≤ 11`), then for EVERY hubcap member `(x, y, v) ∈ members`,
    either `reduceAxleRec` succeeds on a refinement `st_red` matching `cartDeg`, or the active outlet
    sum on `(x, y)` plus `500` is at most `(v + 500).toNat`. -/
theorem verifyHubcapMembersRec_sound (deg : Nat) (cartDeg : Nat → Nat) (h_deg : deg ≤ 11)
    (st : Nat) (h_match : MatchesCartState deg cartDeg st)
    (shiftedTable : List (List FastPosOut))
    (h_table : ∀ row ∈ shiftedTable, ∀ po ∈ row, validFastPosOut deg po = true)
    (members : List (Nat × Nat × Int)) :
    ∀ (hs : HintStream),
      (verifyHubcapMembersRec deg st shiftedTable members hs).1 = true →
      ∀ m ∈ members,
        (∃ st_red hs_red, MatchesCartState deg cartDeg st_red ∧ (reduceAxleRec deg 64 [st_red] hs_red).1 = true) ∨
        500 + activeOutletSum deg cartDeg
          (if Nat.beq m.1 m.2.1 then lookupListRec [] shiftedTable m.1
           else lookupListRec [] shiftedTable m.1 ++ lookupListRec [] shiftedTable m.2.1) ≤
          ((m.2.2 + 500).toNat : Int) := by
  induction members with
  | nil =>
    intro _ _ _ hm; contradiction
  | cons m rest ih =>
    intro hs h_ok m' hm'
    rw [verifyHubcapMembersRec_cons] at h_ok
    rcases m with ⟨x, y, v⟩
    dsimp only at h_ok
    simp only [strictNat_eq] at h_ok
    let outsX := lookupListRec [] shiftedTable x
    let outsY := lookupListRec [] shiftedTable y
    let initRem :=
      @Bool.rec (fun _ => List FastPosOut)
        outsX
        (appendFastPosOut outsX outsY)
        (!Nat.beq x y)
    let resCB := checkBoundRec deg 20 st 500 [] initRem [] (v + 500).toNat hs
    change (@Bool.rec (fun _ => Bool × HintStream) (false, resCB.2)
      (verifyHubcapMembersRec deg st shiftedTable rest resCB.2) resCB.1).1 = true at h_ok
    cases h_cb : resCB.1 with
    | false =>
      rw [h_cb] at h_ok; dsimp only at h_ok; contradiction
    | true =>
      rw [h_cb] at h_ok; dsimp only at h_ok
      rcases List.mem_cons.mp hm' with rfl | hm_rest
      · dsimp only
        have h_init_valid : ∀ po ∈ initRem, validFastPosOut deg po = true := by
          dsimp [initRem]
          cases (!Nat.beq x y) with
          | false =>
            exact validFastPosOut_lookupListRec deg shiftedTable h_table x
          | true =>
            dsimp only
            rw [appendFastPosOut_eq_append]
            intro po hpo
            rcases List.mem_append.mp hpo with hX | hY
            · exact validFastPosOut_lookupListRec deg shiftedTable h_table x po hX
            · exact validFastPosOut_lookupListRec deg shiftedTable h_table y po hY
        rcases checkBoundRec_sound deg cartDeg h_deg 20 st 500 [] initRem [] (v + 500).toNat hs
          h_match (by intro _ h; contradiction) h_init_valid (by intro _ h; contradiction) h_cb with h_red | h_bound
        · exact Or.inl h_red
        · right
          have h_init_eq : initRem = (if Nat.beq x y then outsX else outsX ++ outsY) := by
            dsimp [initRem]
            cases Nat.beq x y with
            | true => rfl
            | false => exact appendFastPosOut_eq_append outsX outsY
          rw [← h_init_eq]
          simpa [activeOutletSum] using h_bound
      · exact ih resCB.2 h_ok m' hm_rest

theorem validFastPosOut_getShiftedTableForDeg_7 :
    (getShiftedTableForDeg 7).all (fun row => row.all (validFastPosOut 7)) = true := by decide

theorem validFastPosOut_getShiftedTableForDeg_8 :
    (getShiftedTableForDeg 8).all (fun row => row.all (validFastPosOut 8)) = true := by decide

theorem validFastPosOut_getShiftedTableForDeg_9 :
    (getShiftedTableForDeg 9).all (fun row => row.all (validFastPosOut 9)) = true := by decide

theorem validFastPosOut_getShiftedTableForDeg_10 :
    (getShiftedTableForDeg 10).all (fun row => row.all (validFastPosOut 10)) = true := by decide

theorem validFastPosOut_getShiftedTableForDeg_11 :
    (getShiftedTableForDeg 11).all (fun row => row.all (validFastPosOut 11)) = true := by decide

theorem validFastPosOut_getShiftedTableForDeg (deg : Nat)
    (h_deg : deg = 7 ∨ deg = 8 ∨ deg = 9 ∨ deg = 10 ∨ deg = 11) :
    ∀ row ∈ getShiftedTableForDeg deg, ∀ po ∈ row, validFastPosOut deg po = true := by
  intro row hrow po hpo
  rcases h_deg with rfl | rfl | rfl | rfl | rfl
  · exact List.all_eq_true.mp (List.all_eq_true.mp validFastPosOut_getShiftedTableForDeg_7 row hrow) po hpo
  · exact List.all_eq_true.mp (List.all_eq_true.mp validFastPosOut_getShiftedTableForDeg_8 row hrow) po hpo
  · exact List.all_eq_true.mp (List.all_eq_true.mp validFastPosOut_getShiftedTableForDeg_9 row hrow) po hpo
  · exact List.all_eq_true.mp (List.all_eq_true.mp validFastPosOut_getShiftedTableForDeg_10 row hrow) po hpo
  · exact List.all_eq_true.mp (List.all_eq_true.mp validFastPosOut_getShiftedTableForDeg_11 row hrow) po hpo

/-!
### Stage K.1: `pushRefinementsRec`, `initIsoVertsRec`, and `reduceAxleRec` Inductive Soundness
-/

/-- Pure 5-bit lane upper degree decoder matching `getUppStrict deg st p` for `1 ≤ p`. -/
def laneUpp (m : Nat) : Nat :=
  if Nat.ble 16 m then 12
  else if Nat.ble 8 m then 8
  else if Nat.ble 4 m then 7
  else if Nat.ble 2 m then 6
  else 5

/-- Pure 5-bit lane highest-bit mask matching `highBit` in `pushRefinementsRec`. -/
def laneHighBit (m : Nat) : Nat :=
  if Nat.ble 16 m then 16
  else if Nat.ble 8 m then 8
  else if Nat.ble 4 m then 4
  else 2

theorem getUppStrict_eq_laneUpp (deg st p : Nat) (hp : 1 ≤ p) :
    getUppStrict deg st p = laneUpp (getLaneNat st p) := by
  unfold getUppStrict laneUpp
  have h0 : Nat.beq p 0 = false := by cases p <;> first | omega | rfl
  rw [h0]
  dsimp only
  rw [strictNat_eq]
  cases Nat.ble 16 (getLaneNat st p) <;>
  cases Nat.ble 8 (getLaneNat st p) <;>
  cases Nat.ble 4 (getLaneNat st p) <;>
  cases Nat.ble 2 (getLaneNat st p) <;> rfl

theorem getUppStrict_zero (deg st : Nat) :
    getUppStrict deg st 0 = deg := rfl

theorem laneUpp_highBit_spec_aux :
    (List.range 32).all (fun m =>
      (Nat.xor m (laneHighBit m) ≤ 31) &&
      (List.range 5).all (fun b =>
        !(m.testBit b) ||
        (b == degBitIdx (laneUpp m)) ||
        ((!Nat.beq (Nat.land m (Nat.sub m 1)) 0) &&
         (Nat.xor m (laneHighBit m)).testBit b))) = true := by decide

theorem laneXor_le_31 {m : Nat} (hm : m ≤ 31) :
    Nat.xor m (laneHighBit m) ≤ 31 := by
  have h_mem : m ∈ List.range 32 := List.mem_range.mpr (by omega)
  have h_row := Bool.and_eq_true_iff.mp (List.all_eq_true.mp laneUpp_highBit_spec_aux m h_mem)
  exact of_decide_eq_true h_row.1

theorem laneUpp_highBit_cases {m b : Nat} (hm : m ≤ 31) (hb : b < 5) (htb : m.testBit b = true) :
    b = degBitIdx (laneUpp m) ∨
    ((!Nat.beq (Nat.land m (Nat.sub m 1)) 0) = true ∧
     (Nat.xor m (laneHighBit m)).testBit b = true) := by
  have h_mem : m ∈ List.range 32 := List.mem_range.mpr (by omega)
  have h_bmem : b ∈ List.range 5 := List.mem_range.mpr hb
  have h_row := Bool.and_eq_true_iff.mp (List.all_eq_true.mp laneUpp_highBit_spec_aux m h_mem)
  have h_cell := List.all_eq_true.mp h_row.2 b h_bmem
  rw [htb] at h_cell
  dsimp at h_cell
  rcases Bool.or_eq_true_iff.mp h_cell with h_eq | h_ref
  · exact Or.inl (beq_iff_eq.mp h_eq)
  · exact Or.inr (Bool.and_eq_true_iff.mp h_ref)

/-- Bounded SWAR cartwheel state predicate: `MatchesCartState` plus 5-bit lane bound `≤ 31` on `1 ≤ p ≤ 5 * deg`. -/
def MatchesCartState31 (deg : Nat) (cartDeg : Nat → Nat) (st : Nat) : Prop :=
  MatchesCartState deg cartDeg st ∧ ∀ p, 1 ≤ p → p ≤ 5 * deg → getLaneNat st p ≤ 31

theorem eq_of_lt_64_of_testBit_eq {a b : Nat} (ha : a < 64) (hb : b < 64)
    (h : ∀ i < 6, a.testBit i = b.testBit i) : a = b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i < 6
  · exact h i hi
  · have h2 : 64 ≤ 2 ^ i := by
      have : 6 ≤ i := by omega
      calc 64 = 2 ^ 6 := rfl
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) this
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha h2),
        Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb h2)]

theorem getLaneNat_setLaneNat_self (st v val : Nat) (hv : v < 60) (hval : val < 64) :
    getLaneNat (setLaneNat st v val) v = val := by
  apply eq_of_lt_64_of_testBit_eq (getLaneNat_lt_64 _ _) hval
  intro i hi
  exact testBit_getLaneNat_setLaneNat_self st v val hv hi

theorem getLaneNat_setLaneNat_ne (st v val p : Nat) (hp : p < 60) (hne : p ≠ v) :
    getLaneNat (setLaneNat st v val) p = getLaneNat st p := by
  apply eq_of_lt_64_of_testBit_eq (getLaneNat_lt_64 _ _) (getLaneNat_lt_64 _ _)
  intro i hi
  exact testBit_getLaneNat_setLaneNat_ne st v val p hp hne hi

theorem getLaneNat_setLaneNat_le_31 (st v val p : Nat) (hp : p < 60)
    (h_st : getLaneNat st p ≤ 31) (h_val : val ≤ 31) :
    getLaneNat (setLaneNat st v val) p ≤ 31 := by
  by_cases hpv : p = v
  · subst hpv
    rw [getLaneNat_setLaneNat_self st p val hp (by omega)]
    exact h_val
  · rw [getLaneNat_setLaneNat_ne st v val p hp hpv]
    exact h_st

theorem matchesCartState31_getInitStateForDeg (deg : Nat) (cartDeg : Nat → Nat)
    (h_deg : deg = 7 ∨ deg = 8 ∨ deg = 9 ∨ deg = 10 ∨ deg = 11) :
    MatchesCartState31 deg cartDeg (getInitStateForDeg deg) := by
  refine ⟨matchesCartState_getInitStateForDeg deg cartDeg h_deg, ?_⟩
  intro p hp1 hp2
  rw [getLaneNat_initStateForDeg_eq_31 deg h_deg hp1 hp2]
  exact Nat.le_refl 31

theorem matchesCartState31_cond_split (deg : Nat) (cartDeg : Nat → Nat) (st v : Nat) (m : Int)
    (h_deg : deg ≤ 11) (h_match31 : MatchesCartState31 deg cartDeg st) :
    let maskTrue := condMaskNat m
    let maskFalse := Nat.xor 31 maskTrue
    let curLane := getLaneNat st v
    MatchesCartState31 deg cartDeg (setLaneNat st v (Nat.land curLane maskTrue)) ∨
    MatchesCartState31 deg cartDeg (setLaneNat st v (Nat.land curLane maskFalse)) := by
  intro maskTrue maskFalse curLane
  have h_bound (mask : Nat) :
      ∀ p, 1 ≤ p → p ≤ 5 * deg → getLaneNat (setLaneNat st v (curLane &&& mask)) p ≤ 31 := by
    intro p hp1 hp2
    have hp60 : p < 60 := by omega
    by_cases hpv : p = v
    · subst hpv
      have h_le : getLaneNat st p &&& mask ≤ 31 :=
        Nat.le_trans Nat.and_le_left (h_match31.2 p hp1 hp2)
      rw [getLaneNat_setLaneNat_self st p (getLaneNat st p &&& mask) hp60 (by omega)]
      exact h_le
    · rw [getLaneNat_setLaneNat_ne st v (curLane &&& mask) p hp60 hpv]
      exact h_match31.2 p hp1 hp2
  rcases matchesCartState_cond_split deg cartDeg st v m h_deg h_match31.1 with hT | hF
  · exact Or.inl ⟨hT, h_bound maskTrue⟩
  · exact Or.inr ⟨hF, h_bound maskFalse⟩

/-- Step equation for `pushRefinementsRec` on `iv :: ivs`. -/
theorem pushRefinementsRec_cons_eq (cur img : Nat) (iv : IntVert) (ivs : List IntVert) (stack : List Nat) :
    pushRefinementsRec cur img (iv :: ivs) stack =
      (let v := getImgNat img iv.u
       if Nat.ble 1 v then
         let m := getLaneNat cur v
         if !Nat.beq (Nat.land m (Nat.sub m 1)) 0 then
           pushRefinementsRec cur img ivs (setLaneNat cur v (Nat.xor m (laneHighBit m)) :: stack)
         else
           pushRefinementsRec cur img ivs stack
       else
         pushRefinementsRec cur img ivs stack) := by
  cases iv with
  | mk ivu ivd ivw ivcyc =>
    unfold pushRefinementsRec laneHighBit
    dsimp only
    simp only [strictNat_eq]
    cases Nat.ble 1 (getImgNat img ivu) with
    | false => rfl
    | true =>
      dsimp only
      cases (!Nat.beq (Nat.land (getLaneNat cur (getImgNat img ivu)) (Nat.sub (getLaneNat cur (getImgNat img ivu)) 1)) 0) with
      | false => rfl
      | true =>
        dsimp only
        cases Nat.ble 16 (getLaneNat cur (getImgNat img ivu)) <;>
        cases Nat.ble 8 (getLaneNat cur (getImgNat img ivu)) <;>
        cases Nat.ble 4 (getLaneNat cur (getImgNat img ivu)) <;> rfl

/-- Monotonicity of `pushRefinementsRec`: every state already in `stack` remains in `pushRefinementsRec cur img ivs stack`. -/
theorem mem_pushRefinementsRec_of_mem (cur img : Nat) (ivs : List IntVert) :
    ∀ (stack : List Nat) {s : Nat}, s ∈ stack → s ∈ pushRefinementsRec cur img ivs stack := by
  induction ivs with
  | nil =>
    intro stack s hs
    exact hs
  | cons iv ivs ih =>
    intro stack s hs
    rw [pushRefinementsRec_cons_eq]
    dsimp only
    split
    · split
      · exact ih _ (List.mem_cons_of_mem _ hs)
      · exact ih _ hs
    · exact ih _ hs

/-- Partition Lemma for `pushRefinementsRec`:
    Given `MatchesCartState31 deg cartDeg cur` and `∀ iv ∈ ivs, getImgNat img iv.u ≤ 5 * deg`,
    either every interior vertex `iv ∈ ivs` with `1 ≤ getImgNat img iv.u` already has
    `degBitIdx (cartDeg (getImgNat img iv.u)) = degBitIdx (getUppStrict deg cur (getImgNat img iv.u))`,
    or `pushRefinementsRec cur img ivs stack` contains a refined state `nextSt` satisfying `MatchesCartState31 deg cartDeg nextSt`. -/
theorem matchesCartState31_pushRefinementsRec_or_exact (deg : Nat) (cartDeg : Nat → Nat)
    (cur img : Nat) (ivs : List IntVert) (h_deg : deg ≤ 11)
    (h_cur : MatchesCartState31 deg cartDeg cur)
    (h_ivs_le : ∀ iv ∈ ivs, getImgNat img iv.u ≤ 5 * deg) :
    ∀ (stack : List Nat),
      (∀ iv ∈ ivs, 1 ≤ getImgNat img iv.u →
        degBitIdx (cartDeg (getImgNat img iv.u)) = degBitIdx (getUppStrict deg cur (getImgNat img iv.u))) ∨
      (∃ nextSt ∈ pushRefinementsRec cur img ivs stack, MatchesCartState31 deg cartDeg nextSt) := by
  induction ivs with
  | nil =>
    intro _
    left
    intro _ h_mem
    cases h_mem
  | cons iv ivs ih =>
    intro stack
    rw [pushRefinementsRec_cons_eq]
    dsimp only
    let v := getImgNat img iv.u
    have hv_le : v ≤ 5 * deg := h_ivs_le iv List.mem_cons_self
    have h_ivs_tail : ∀ iv' ∈ ivs, getImgNat img iv'.u ≤ 5 * deg :=
      fun iv' hm => h_ivs_le iv' (List.mem_cons_of_mem _ hm)
    cases hv1 : Nat.ble 1 v with
    | false =>
      have hv_not : ¬(1 ≤ v) := fun h => by
        rw [Nat.ble_eq_true_of_le h] at hv1; contradiction
      rcases ih h_ivs_tail stack with h_all | h_ex
      · left
        intro iv' hm hv'
        rcases List.mem_cons.mp hm with rfl | hm_tail
        · exact False.elim (hv_not hv')
        · exact h_all iv' hm_tail hv'
      · exact Or.inr h_ex
    | true =>
      have hv_ge1 : 1 ≤ v := Nat.le_of_ble_eq_true hv1
      let m := getLaneNat cur v
      have hm_le : m ≤ 31 := h_cur.2 v hv_ge1 hv_le
      have h_tb : m.testBit (degBitIdx (cartDeg v)) = true := h_cur.1 v hv_ge1 hv_le
      have h_upp : getUppStrict deg cur v = laneUpp m := getUppStrict_eq_laneUpp deg cur v hv_ge1
      rcases laneUpp_highBit_cases hm_le (degBitIdx_lt_5 (cartDeg v)) h_tb with h_eq_idx | ⟨h_multi, h_xor_tb⟩
      · -- Head vertex `iv` already has exact degree bit index!
        cases h_cond : (!Nat.beq (Nat.land m (Nat.sub m 1)) 0) with
        | false =>
          rcases ih h_ivs_tail stack with h_all | h_ex
          · left
            intro iv' hm hv'
            rcases List.mem_cons.mp hm with rfl | hm_tail
            · rw [h_upp]; exact h_eq_idx
            · exact h_all iv' hm_tail hv'
          · right
            simpa [h_cond] using h_ex
        | true =>
          rcases ih h_ivs_tail (setLaneNat cur v (Nat.xor m (laneHighBit m)) :: stack) with h_all | h_ex
          · left
            intro iv' hm hv'
            rcases List.mem_cons.mp hm with rfl | hm_tail
            · rw [h_upp]; exact h_eq_idx
            · exact h_all iv' hm_tail hv'
          · right
            simpa [h_cond] using h_ex
      · -- Head vertex `iv` pushes a valid refinement `nextSt` onto the stack!
        right
        let nextSt := setLaneNat cur v (Nat.xor m (laneHighBit m))
        have h_next_match : MatchesCartState deg cartDeg nextSt := by
          intro p hp1 hp2
          have hv60 : v < 60 := by omega
          have hp60 : p < 60 := by omega
          by_cases hpv : p = v
          · subst hpv
            rw [testBit_getLaneNat_setLaneNat_self cur v _ hv60 (degBitIdx_lt_6 _)]
            exact h_xor_tb
          · rw [testBit_getLaneNat_setLaneNat_ne cur v _ p hp60 hpv (degBitIdx_lt_6 _)]
            exact h_cur.1 p hp1 hp2
        have h_next_le31 : ∀ p, 1 ≤ p → p ≤ 5 * deg → getLaneNat nextSt p ≤ 31 := by
          intro p hp1 hp2
          exact getLaneNat_setLaneNat_le_31 cur v (Nat.xor m (laneHighBit m)) p (by omega)
            (h_cur.2 p hp1 hp2) (laneXor_le_31 hm_le)
        refine ⟨nextSt, ?_, ⟨h_next_match, h_next_le31⟩⟩
        change nextSt ∈ (if (!Nat.beq (Nat.land m (Nat.sub m 1)) 0) = true then
          pushRefinementsRec cur img ivs (nextSt :: stack) else pushRefinementsRec cur img ivs stack)
        rw [if_pos h_multi]
        exact mem_pushRefinementsRec_of_mem cur img ivs (nextSt :: stack) List.mem_cons_self

/-- Inner loop helper for `initIsoVertsRec` to prove vertex degree & range invariants by induction on `ivs`. -/
noncomputable def initIsoVertsLoop (deg ring : Nat) (st : Nat) (img : Nat) (ivs : List IntVert) (invMap usedMask : Nat) : Option (Nat × Nat) :=
  List.rec
    (motive := fun _ => Nat → Nat → Option (Nat × Nat))
    (fun invMap usedMask => some (invMap, usedMask))
    (fun iv _ ih invMap usedMask =>
      match iv with
      | IntVert.mk ivu ivd _ _ =>
        strictNat (getImgNat img ivu) fun fu =>
        Bool.rec
          none
          (Bool.rec
            (Bool.rec
              none
              (let okFan :=
                 Bool.rec
                   (let i := Nat.add (Nat.mod (Nat.sub fu 1) deg) 1
                    strictNat (getExactDegStrict deg st i) fun ex =>
                    !Nat.beq ex 0 && Nat.ble (Nat.add (Nat.div (Nat.sub fu 1) deg) 4) ex)
                   true
                   (Nat.ble fu (Nat.mul 2 deg))
               Bool.rec
                 none
                 (strictNat (Nat.lor usedMask (Nat.shiftLeft 1 fu)) fun usedMask' =>
                  strictNat (setLaneNat invMap fu (Nat.sub ivu (Nat.add ring 1))) fun invMap' =>
                  ih invMap' usedMask')
                 okFan)
              (Nat.beq ivd (getUppStrict deg st fu)))
            none
            (!Nat.beq (Nat.land (Nat.shiftRight usedMask fu) 1) 0))
          (Nat.ble fu (Nat.mul 5 deg)))
    ivs invMap usedMask

theorem initIsoVertsRec_eq_loop (deg ring st img : Nat) (ivs : List IntVert) :
    initIsoVertsRec deg ring st img ivs = initIsoVertsLoop deg ring st img ivs 0 0 := rfl

noncomputable def okFanBool (deg st fu : Nat) : Bool :=
  Bool.rec
    (let i := Nat.add (Nat.mod (Nat.sub fu 1) deg) 1
     strictNat (getExactDegStrict deg st i) fun ex =>
     !Nat.beq ex 0 && Nat.ble (Nat.add (Nat.div (Nat.sub fu 1) deg) 4) ex)
    true
    (Nat.ble fu (Nat.mul 2 deg))

theorem initIsoVertsLoop_cons_eq (deg ring st img : Nat) (iv : IntVert) (ivs : List IntVert) (invMap usedMask : Nat) :
    initIsoVertsLoop deg ring st img (iv :: ivs) invMap usedMask =
      (let fu := getImgNat img iv.u
       if Nat.ble fu (Nat.mul 5 deg) then
         if !Nat.beq (Nat.land (Nat.shiftRight usedMask fu) 1) 0 then
           none
         else if Nat.beq iv.d (getUppStrict deg st fu) then
           if okFanBool deg st fu then
             initIsoVertsLoop deg ring st img ivs
               (setLaneNat invMap fu (Nat.sub iv.u (Nat.add ring 1)))
               (Nat.lor usedMask (Nat.shiftLeft 1 fu))
           else
             none
         else
           none
       else
         none) := by
  cases iv with
  | mk ivu ivd ivw ivcyc =>
    unfold initIsoVertsLoop
    dsimp only
    rw [strictNat_eq]
    cases Nat.ble (getImgNat img ivu) (Nat.mul 5 deg) with
    | false => rfl
    | true =>
      dsimp only
      cases (!Nat.beq (Nat.land (Nat.shiftRight usedMask (getImgNat img ivu)) 1) 0) with
      | true => rfl
      | false =>
        dsimp only
        cases Nat.beq ivd (getUppStrict deg st (getImgNat img ivu)) with
        | false => rfl
        | true =>
          dsimp only
          change @Bool.rec (fun _ => Option (Nat × Nat)) none
            (strictNat (Nat.lor usedMask (Nat.shiftLeft 1 (getImgNat img ivu))) fun usedMask' =>
             strictNat (setLaneNat invMap (getImgNat img ivu) (Nat.sub ivu (Nat.add ring 1))) fun invMap' =>
             initIsoVertsLoop deg ring st img ivs invMap' usedMask')
            (okFanBool deg st (getImgNat img ivu)) = _
          cases okFanBool deg st (getImgNat img ivu) with
          | false => rfl
          | true =>
            dsimp only
            rw [strictNat_eq, strictNat_eq]
            rfl

theorem initIsoVertsLoop_sound (deg ring st img : Nat) (ivs : List IntVert) :
    ∀ (invMap usedMask : Nat) {res : Nat × Nat},
      initIsoVertsLoop deg ring st img ivs invMap usedMask = some res →
      ∀ iv ∈ ivs, getImgNat img iv.u ≤ 5 * deg ∧ iv.d = getUppStrict deg st (getImgNat img iv.u) := by
  induction ivs with
  | nil =>
    intro _ _ _ _ iv h_mem
    cases h_mem
  | cons iv ivs ih =>
    intro invMap usedMask res h_some iv' h_mem
    rw [initIsoVertsLoop_cons_eq] at h_some
    dsimp only at h_some
    let fu := getImgNat img iv.u
    cases h_ble : Nat.ble fu (Nat.mul 5 deg) with
    | false =>
      rw [h_ble] at h_some; contradiction
    | true =>
      rw [h_ble] at h_some
      cases h_used : (!Nat.beq (Nat.land (Nat.shiftRight usedMask fu) 1) 0) with
      | true =>
        rw [h_used] at h_some; contradiction
      | false =>
        rw [h_used] at h_some
        cases h_upp : Nat.beq iv.d (getUppStrict deg st fu) with
        | false =>
          rw [h_upp] at h_some; contradiction
        | true =>
          rw [h_upp] at h_some
          cases h_fan : okFanBool deg st fu with
          | false =>
            rw [h_fan] at h_some; contradiction
          | true =>
            rw [h_fan] at h_some
            simp only [ite_true] at h_some
            rcases List.mem_cons.mp h_mem with rfl | h_tail
            · exact ⟨Nat.le_of_ble_eq_true h_ble, Nat.beq_eq.mp h_upp⟩
            · exact ih _ _ h_some iv' h_tail

theorem checkIsoRec_intVerts_sound (ring adjMat : Nat) (intVerts : List IntVert) (deg st img : Nat)
    (h_iso : checkIsoRec ring adjMat intVerts deg st img = true) :
    ∀ iv ∈ intVerts, getImgNat img iv.u ≤ 5 * deg ∧ iv.d = getUppStrict deg st (getImgNat img iv.u) := by
  unfold checkIsoRec at h_iso
  rw [initIsoVertsRec_eq_loop] at h_iso
  cases h_init : initIsoVertsLoop deg ring st img intVerts 0 0 with
  | none =>
    rw [h_init] at h_iso; contradiction
  | some p =>
    exact initIsoVertsLoop_sound deg ring st img intVerts 0 0 h_init

/-- Predicate characterizing that a cartwheel degree assignment `cartDeg` has a verified
    reducible configuration embedding (`rootedSubConfRec` + `checkIsoRec`) whose interior vertex
    degrees `iv.d` match `cartDeg` at every cartwheel vertex `1 ≤ v ≤ 5 * deg`. -/
def HasExactReducedAxle (deg : Nat) (cartDeg : Nat → Nat) : Prop :=
  ∃ (cur h x y : Nat) (cw : Bool) (img : Nat),
    MatchesCartState31 deg cartDeg cur ∧
    let fc := lookupFastConfRec h
    rootedSubConfRec deg cur fc.z0 fc.z1 fc.qSteps x y cw = some img ∧
    checkIsoRec fc.ring fc.adjMat fc.intVerts deg cur img = true ∧
    ∀ iv ∈ fc.intVerts,
      getImgNat img iv.u ≤ 5 * deg ∧
      iv.d = getUppStrict deg cur (getImgNat img iv.u) ∧
      (1 ≤ getImgNat img iv.u → degBitIdx (cartDeg (getImgNat img iv.u)) = degBitIdx iv.d)

theorem reduceAxleRec_succ_eq (deg fuel : Nat) (cur : Nat) (rest : List Nat) (hs : HintStream) :
    reduceAxleRec deg (fuel + 1) (cur :: rest) hs =
      (match popHintRec hs with
       | none => (false, hs)
       | some (p, hs') =>
         let h := Nat.shiftRight p 13
         let x := Nat.land (Nat.shiftRight p 7) 63
         let y := Nat.land (Nat.shiftRight p 1) 63
         let cw := Nat.beq (Nat.land p 1) 1
         let fc := lookupFastConfRec h
         match rootedSubConfRec deg cur fc.z0 fc.z1 fc.qSteps x y cw with
         | none => (false, hs')
         | some img =>
           Bool.rec
             (false, hs')
             (reduceAxleRec deg fuel (pushRefinementsRec cur img fc.intVerts rest) hs')
             (checkIsoRec fc.ring fc.adjMat fc.intVerts deg cur img)) := by
  unfold reduceAxleRec
  dsimp only
  cases popHintRec hs with
  | none => rfl
  | some phs =>
    rcases phs with ⟨p, hs'⟩
    dsimp only
    simp only [strictNat_eq]
    cases lookupFastConfRec (Nat.shiftRight p 13) with
    | mk idx ring z0 z1 adjMat qSteps intVerts =>
      dsimp only
      rfl

/-- Inductive Soundness of `reduceAxleRec`:
    if `(reduceAxleRec deg fuel stack hs).1 = true` and `stack` contains at least one state `st`
    satisfying `MatchesCartState31 deg cartDeg st`, then `HasExactReducedAxle deg cartDeg` holds. -/
theorem reduceAxleRec_sound (deg : Nat) (cartDeg : Nat → Nat) (h_deg : deg ≤ 11) :
    ∀ (fuel : Nat) (stack : List Nat) (hs : HintStream),
      (∃ st ∈ stack, MatchesCartState31 deg cartDeg st) →
      (reduceAxleRec deg fuel stack hs).1 = true →
      HasExactReducedAxle deg cartDeg := by
  intro fuel
  induction fuel with
  | zero =>
    intro stack hs ⟨st, h_mem, _⟩ h_ok
    cases stack with
    | nil => cases h_mem
    | cons cur rest =>
      change (false : Bool) = true at h_ok
      contradiction
  | succ fuel ih =>
    intro stack hs ⟨st, h_mem, h_st⟩ h_ok
    cases stack with
    | nil => cases h_mem
    | cons cur rest =>
      rw [reduceAxleRec_succ_eq] at h_ok
      dsimp only at h_ok
      cases h_pop : popHintRec hs with
      | none =>
        rw [h_pop] at h_ok; contradiction
      | some phs =>
        rcases phs with ⟨p, hs'⟩
        rw [h_pop] at h_ok
        dsimp only at h_ok
        let h := Nat.shiftRight p 13
        let x := Nat.land (Nat.shiftRight p 7) 63
        let y := Nat.land (Nat.shiftRight p 1) 63
        let cw := Nat.beq (Nat.land p 1) 1
        let fc := lookupFastConfRec h
        cases h_sub : rootedSubConfRec deg cur fc.z0 fc.z1 fc.qSteps x y cw with
        | none =>
          rw [h_sub] at h_ok; contradiction
        | some img =>
          rw [h_sub] at h_ok
          dsimp only at h_ok
          cases h_iso : checkIsoRec fc.ring fc.adjMat fc.intVerts deg cur img with
          | false =>
            rw [h_iso] at h_ok; dsimp at h_ok; contradiction
          | true =>
            rw [h_iso] at h_ok
            dsimp only at h_ok
            rcases List.mem_cons.mp h_mem with rfl | h_in_rest
            · -- `st = cur`
              have h_ivs := checkIsoRec_intVerts_sound fc.ring fc.adjMat fc.intVerts deg st img h_iso
              have h_ivs_le : ∀ iv ∈ fc.intVerts, getImgNat img iv.u ≤ 5 * deg :=
                fun iv hm => (h_ivs iv hm).1
              rcases matchesCartState31_pushRefinementsRec_or_exact deg cartDeg st img fc.intVerts h_deg h_st h_ivs_le rest with h_exact | h_next
              · refine ⟨st, h, x, y, cw, img, h_st, h_sub, h_iso, ?_⟩
                intro iv hm
                have ⟨hle, hd⟩ := h_ivs iv hm
                refine ⟨hle, hd, ?_⟩
                intro hv1
                rw [hd]
                exact h_exact iv hm hv1
              · exact ih (pushRefinementsRec st img fc.intVerts rest) hs' h_next h_ok
            · -- `st ∈ rest`
              exact ih (pushRefinementsRec cur img fc.intVerts rest) hs'
                ⟨st, mem_pushRefinementsRec_of_mem cur img fc.intVerts rest h_in_rest, h_st⟩ h_ok

/-!
### Stage K.2: `symForcedRec`, `extractCondsRec`, and Full Semantic Soundness of `verifyTree`
-/

/-- Rotational shift of a cartwheel position `p0` by `x_shift` (`0 ≤ x_shift < deg`) within its `deg`-ring. -/
def shiftCartPos (deg x_shift p0 : Nat) : Nat :=
  if !Nat.ble deg (Nat.add x_shift (Nat.mod (Nat.sub p0 1) deg)) then
    Nat.add p0 x_shift
  else
    Nat.sub (Nat.add p0 x_shift) deg

/-- Reflection of a cartwheel position `1 ≤ p ≤ 2 * deg` across spoke 1. -/
def reflCartPos (deg p : Nat) : Nat :=
  if Nat.ble p deg then
    Nat.add (Nat.sub deg p) 1
  else if !Nat.ble (Nat.mul 2 deg) p then
    Nat.sub (Nat.mul 3 deg) p
  else
    Nat.mul 2 deg

/-- Combined rotational/reflectional image of cartwheel position `p0`. -/
def symCartPos (deg x_shift : Nat) (refl : Bool) (p0 : Nat) : Nat :=
  if refl then reflCartPos deg (shiftCartPos deg x_shift p0)
  else shiftCartPos deg x_shift p0

/-- Rotated/reflected cartwheel degree assignment induced by `(x_shift, refl)`. -/
def symCartDeg (deg x_shift : Nat) (refl : Bool) (cartDeg : Nat → Nat) : Nat → Nat :=
  fun p0 => cartDeg (symCartPos deg x_shift refl p0)

theorem shiftCartPos_bounds {deg x_shift p0 : Nat} (h_deg : 1 ≤ deg) (h_shift : x_shift < deg)
    (hp1 : 1 ≤ p0) (hp2 : p0 ≤ 2 * deg) :
    1 ≤ shiftCartPos deg x_shift p0 ∧ shiftCartPos deg x_shift p0 ≤ 2 * deg := by
  unfold shiftCartPos
  have h_div_mod := Nat.div_add_mod (p0 - 1) deg
  have h_mod_lt : (p0 - 1) % deg < deg := Nat.mod_lt (p0 - 1) (by omega)
  have h_div_le : (p0 - 1) / deg ≤ 1 := by
    have h_lt : p0 - 1 < 2 * deg := by omega
    have h_div_lt : (p0 - 1) / deg < 2 := (Nat.div_lt_iff_lt_mul (by omega)).mpr h_lt
    omega
  have h_prod_le : deg * ((p0 - 1) / deg) ≤ deg := by
    have := Nat.mul_le_mul_left deg h_div_le
    omega
  cases h_cond : Nat.ble deg (Nat.add x_shift (Nat.mod (Nat.sub p0 1) deg)) with
  | false =>
    have h_lt_deg : x_shift + (p0 - 1) % deg < deg :=
      Classical.byContradiction fun h_ge => by
        have h_le : deg ≤ Nat.add x_shift (Nat.mod (Nat.sub p0 1) deg) := by
          change deg ≤ x_shift + (p0 - 1) % deg
          omega
        rw [Nat.ble_eq_true_of_le h_le] at h_cond
        contradiction
    simp only [Bool.not_false, ite_true]
    change 1 ≤ p0 + x_shift ∧ p0 + x_shift ≤ 2 * deg
    omega
  | true =>
    have h_ge_deg : deg ≤ x_shift + (p0 - 1) % deg := Nat.le_of_ble_eq_true h_cond
    simp only [Bool.not_true]
    change 1 ≤ p0 + x_shift - deg ∧ p0 + x_shift - deg ≤ 2 * deg
    omega

theorem reflCartPos_bounds {deg p : Nat} (h_deg : 1 ≤ deg) (hp1 : 1 ≤ p) (hp2 : p ≤ 2 * deg) :
    1 ≤ reflCartPos deg p ∧ reflCartPos deg p ≤ 2 * deg := by
  unfold reflCartPos
  cases h1 : Nat.ble p deg with
  | true =>
    have hp_le : p ≤ deg := Nat.le_of_ble_eq_true h1
    simp only [ite_true]
    change 1 ≤ deg - p + 1 ∧ deg - p + 1 ≤ 2 * deg
    omega
  | false =>
    have hp_gt : deg < p :=
      Classical.byContradiction fun h_le => by
        rw [Nat.ble_eq_true_of_le (by omega)] at h1; contradiction
    cases h2 : Nat.ble (Nat.mul 2 deg) p with
    | false =>
      have hp_lt : p < 2 * deg :=
        Classical.byContradiction fun h_ge => by
          have h_le : Nat.mul 2 deg ≤ p := by change 2 * deg ≤ p; omega
          rw [Nat.ble_eq_true_of_le h_le] at h2; contradiction
      simp only [Bool.not_false, ite_true]
      change 1 ≤ 3 * deg - p ∧ 3 * deg - p ≤ 2 * deg
      omega
    | true =>
      simp only [Bool.not_true]
      change 1 ≤ 2 * deg ∧ 2 * deg ≤ 2 * deg
      omega

theorem symCartPos_bounds {deg x_shift p0 : Nat} (refl : Bool)
    (h_deg : 1 ≤ deg) (h_shift : x_shift < deg) (hp1 : 1 ≤ p0) (hp2 : p0 ≤ 2 * deg) :
    1 ≤ symCartPos deg x_shift refl p0 ∧ symCartPos deg x_shift refl p0 ≤ 2 * deg := by
  unfold symCartPos
  have ⟨hs1, hs2⟩ := shiftCartPos_bounds h_deg h_shift hp1 hp2
  cases refl with
  | false => exact ⟨hs1, hs2⟩
  | true => exact reflCartPos_bounds h_deg hs1 hs2

/-- Inner loop helper for `symForcedRec` to prove condition forcing by structural induction on `conds`. -/
noncomputable def symForcedLoop (st x_shift deg : Nat) (refl : Bool) (conds : List (Nat × Nat)) : Bool :=
  List.rec
    (motive := fun _ => Bool)
    true
    (fun c _ ih =>
      let (p0, bm) := c
      strictNat
        (Bool.rec
          (Nat.sub (Nat.add p0 x_shift) deg)
          (Nat.add p0 x_shift)
          (!Nat.ble deg (Nat.add x_shift (Nat.mod (Nat.sub p0 1) deg))))
        fun p =>
      Bool.rec
        (Bool.rec
          ih
          false
          (!Nat.beq (Nat.land (getLaneNat st p) (Nat.xor 31 bm)) 0))
        (Bool.rec
          false
          (let q :=
             Bool.rec
               (Bool.rec
                 (Nat.mul 2 deg)
                 (Nat.sub (Nat.mul 3 deg) p)
                 (!Nat.ble (Nat.mul 2 deg) p))
               (Nat.add (Nat.sub deg p) 1)
               (Nat.ble p deg)
           Bool.rec
             ih
             false
             (!Nat.beq (Nat.land (getLaneNat st q) (Nat.xor 31 bm)) 0))
          (Nat.ble 1 p && Nat.ble p (Nat.mul 2 deg)))
        refl)
    conds

theorem symForcedRec_eq_loop (st x deg : Nat) (refl : Bool) (conds : List (Nat × Nat)) :
    symForcedRec st x deg refl conds = symForcedLoop st (Nat.sub x 1) deg refl conds := by
  unfold symForcedRec
  rw [strictNat_eq]
  rfl

theorem symForcedLoop_cons_eq (st x_shift deg : Nat) (refl : Bool) (c : Nat × Nat) (conds : List (Nat × Nat)) :
    symForcedLoop st x_shift deg refl (c :: conds) =
      (let p := shiftCartPos deg x_shift c.1
       if refl then
         if Nat.ble 1 p && Nat.ble p (Nat.mul 2 deg) then
           let q := reflCartPos deg p
           if !Nat.beq (Nat.land (getLaneNat st q) (Nat.xor 31 c.2)) 0 then
             false
           else
             symForcedLoop st x_shift deg refl conds
         else
           false
       else
         if !Nat.beq (Nat.land (getLaneNat st p) (Nat.xor 31 c.2)) 0 then
           false
         else
           symForcedLoop st x_shift deg refl conds) := by
  rcases c with ⟨p0, bm⟩
  unfold symForcedLoop shiftCartPos reflCartPos
  dsimp only
  have h_p :
      (@Bool.rec (fun _ => Nat) (Nat.sub (Nat.add p0 x_shift) deg) (Nat.add p0 x_shift)
        (!Nat.ble deg (Nat.add x_shift (Nat.mod (Nat.sub p0 1) deg)))) =
      (if (!Nat.ble deg (Nat.add x_shift (Nat.mod (Nat.sub p0 1) deg))) = true then
        Nat.add p0 x_shift else Nat.sub (Nat.add p0 x_shift) deg) := by
    cases (!Nat.ble deg (Nat.add x_shift (Nat.mod (Nat.sub p0 1) deg))) <;> rfl
  rw [strictNat_eq, h_p]
  let p := if (!Nat.ble deg (Nat.add x_shift (Nat.mod (Nat.sub p0 1) deg))) = true then
    Nat.add p0 x_shift else Nat.sub (Nat.add p0 x_shift) deg
  cases refl with
  | false =>
    dsimp only
    cases (!Nat.beq (Nat.land (getLaneNat st p) (Nat.xor 31 bm)) 0) <;> rfl
  | true =>
    dsimp only
    cases (Nat.ble 1 p && Nat.ble p (Nat.mul 2 deg)) with
    | false => rfl
    | true =>
      dsimp only
      have h_q :
          (@Bool.rec (fun _ => Nat)
            (@Bool.rec (fun _ => Nat) (Nat.mul 2 deg) (Nat.sub (Nat.mul 3 deg) p) (!Nat.ble (Nat.mul 2 deg) p))
            (Nat.add (Nat.sub deg p) 1) (Nat.ble p deg)) =
          (if Nat.ble p deg = true then Nat.add (Nat.sub deg p) 1
           else if (!Nat.ble (Nat.mul 2 deg) p) = true then Nat.sub (Nat.mul 3 deg) p
           else Nat.mul 2 deg) := by
        cases Nat.ble p deg <;> cases (!Nat.ble (Nat.mul 2 deg) p) <;> rfl
      rw [h_q]
      let q := if Nat.ble p deg = true then Nat.add (Nat.sub deg p) 1
               else if (!Nat.ble (Nat.mul 2 deg) p) = true then Nat.sub (Nat.mul 3 deg) p
               else Nat.mul 2 deg
      cases (!Nat.beq (Nat.land (getLaneNat st q) (Nat.xor 31 bm)) 0) <;> rfl

theorem testBit_of_land_xor_31_eq_zero {lane bm d : Nat}
    (h_tb : lane.testBit (degBitIdx d) = true)
    (h_zero : (!Nat.beq (Nat.land lane (Nat.xor 31 bm)) 0) = false) :
    bm.testBit (degBitIdx d) = true := by
  have h_eq : lane &&& (31 ^^^ bm) = 0 := by
    cases h_b : Nat.beq (Nat.land lane (Nat.xor 31 bm)) 0 with
    | true => exact Nat.beq_eq.mp h_b
    | false => rw [h_b] at h_zero; contradiction
  have h_bit : (lane &&& (31 ^^^ bm)).testBit (degBitIdx d) = false := by
    rw [h_eq, Nat.zero_testBit]
  rw [Nat.testBit_and, Nat.testBit_xor, h_tb, testBit_31_degBitIdx d, Bool.true_and] at h_bit
  cases h_bm : bm.testBit (degBitIdx d) with
  | true => rfl
  | false => rw [h_bm] at h_bit; contradiction

/-- Soundness of `symForcedRec`:
    if `MatchesCartState deg cartDeg st`, every `(p0, bm) ∈ conds` has `1 ≤ p0 ≤ 2 * deg`,
    and `symForcedRec st x deg refl conds = true` (with `1 ≤ deg` and `x - 1 < deg`),
    then for every `(p0, bm) ∈ conds`, the rotated/reflected degree assignment
    `symCartDeg deg (x - 1) refl cartDeg` satisfies `bm.testBit (degBitIdx (symCartDeg deg (x - 1) refl cartDeg p0)) = true`. -/
theorem symForcedRec_sound (deg : Nat) (cartDeg : Nat → Nat) (st x : Nat) (refl : Bool)
    (conds : List (Nat × Nat)) (h_deg : 1 ≤ deg) (h_shift : x - 1 < deg)
    (h_match : MatchesCartState deg cartDeg st)
    (h_conds : ∀ c ∈ conds, 1 ≤ c.1 ∧ c.1 ≤ 2 * deg)
    (h_ok : symForcedRec st x deg refl conds = true) :
    ∀ c ∈ conds, c.2.testBit (degBitIdx (symCartDeg deg (x - 1) refl cartDeg c.1)) = true := by
  rw [symForcedRec_eq_loop] at h_ok
  have h_loop :
      ∀ (cs : List (Nat × Nat)),
        (∀ c ∈ cs, 1 ≤ c.1 ∧ c.1 ≤ 2 * deg) →
        symForcedLoop st (x - 1) deg refl cs = true →
        ∀ c ∈ cs, c.2.testBit (degBitIdx (symCartDeg deg (x - 1) refl cartDeg c.1)) = true := by
    intro cs
    induction cs with
    | nil =>
      intro _ _ c hc
      cases hc
    | cons c cs ih =>
      intro h_cs h_cs_ok c' hc'
      rw [symForcedLoop_cons_eq] at h_cs_ok
      dsimp only at h_cs_ok
      have ⟨hp0_1, hp0_2⟩ := h_cs c List.mem_cons_self
      have h_tail : ∀ c'' ∈ cs, 1 ≤ c''.1 ∧ c''.1 ≤ 2 * deg :=
        fun c'' hm => h_cs c'' (List.mem_cons_of_mem _ hm)
      have ⟨hp1, hp2⟩ := shiftCartPos_bounds h_deg h_shift hp0_1 hp0_2
      cases refl with
      | false =>
        cases h_z : (!Nat.beq (Nat.land (getLaneNat st (shiftCartPos deg (x - 1) c.1)) (Nat.xor 31 c.2)) 0) with
        | true =>
          rw [h_z] at h_cs_ok; contradiction
        | false =>
          rw [h_z] at h_cs_ok
          rcases List.mem_cons.mp hc' with rfl | hc_tail
          · unfold symCartDeg symCartPos
            have h_tb : (getLaneNat st (shiftCartPos deg (x - 1) c'.1)).testBit (degBitIdx (cartDeg (shiftCartPos deg (x - 1) c'.1))) = true :=
              h_match (shiftCartPos deg (x - 1) c'.1) hp1 (by omega)
            exact testBit_of_land_xor_31_eq_zero h_tb h_z
          · exact ih h_tail h_cs_ok c' hc_tail
      | true =>
        cases h_p_b : (Nat.ble 1 (shiftCartPos deg (x - 1) c.1) && Nat.ble (shiftCartPos deg (x - 1) c.1) (Nat.mul 2 deg)) with
        | false =>
          rw [h_p_b] at h_cs_ok; contradiction
        | true =>
          rw [h_p_b] at h_cs_ok
          have ⟨hq1, hq2⟩ := reflCartPos_bounds h_deg hp1 hp2
          cases h_z : (!Nat.beq (Nat.land (getLaneNat st (reflCartPos deg (shiftCartPos deg (x - 1) c.1))) (Nat.xor 31 c.2)) 0) with
          | true =>
            rw [h_z] at h_cs_ok; contradiction
          | false =>
            rw [h_z] at h_cs_ok
            simp only [ite_true] at h_cs_ok
            rcases List.mem_cons.mp hc' with rfl | hc_tail
            · unfold symCartDeg symCartPos
              simp only [ite_true]
              have h_tb : (getLaneNat st (reflCartPos deg (shiftCartPos deg (x - 1) c'.1))).testBit
                  (degBitIdx (cartDeg (reflCartPos deg (shiftCartPos deg (x - 1) c'.1)))) = true :=
                h_match (reflCartPos deg (shiftCartPos deg (x - 1) c'.1)) hq1 (by omega)
              exact testBit_of_land_xor_31_eq_zero h_tb h_z
            · exact ih h_tail h_cs_ok c' hc_tail
  exact h_loop conds h_conds h_ok

/-- Inner loop helper for `extractCondsRec` to prove `1 ≤ c.1 ≤ 2 * deg` for all extracted conditions. -/
noncomputable def extractCondsLoop (deg condV condM lev : Nat) (acc0 : List (Nat × Nat)) : Option (List (Nat × Nat)) :=
  Nat.rec
    (motive := fun _ => List (Nat × Nat) → Option (List (Nat × Nat)))
    (fun acc =>
      strictNat (getLaneNat condV 0) fun n =>
      Bool.rec
        none
        (some ((n, getLaneNat condM 0) :: acc))
        (Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg)))
    (fun i ih acc =>
      strictNat (Nat.add i 1) fun idx =>
      strictNat (getLaneNat condV idx) fun n =>
      Bool.rec
        none
        (ih ((n, getLaneNat condM idx) :: acc))
        (Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg)))
    lev acc0

theorem extractCondsRec_eq_loop (deg condV condM lev : Nat) :
    extractCondsRec deg condV condM lev = extractCondsLoop deg condV condM lev [] := rfl

theorem extractCondsLoop_sound (deg condV condM : Nat) :
    ∀ (lev : Nat) (acc res : List (Nat × Nat)),
      (∀ c ∈ acc, 1 ≤ c.1 ∧ c.1 ≤ 2 * deg) →
      extractCondsLoop deg condV condM lev acc = some res →
      ∀ c ∈ res, 1 ≤ c.1 ∧ c.1 ≤ 2 * deg := by
  intro lev
  induction lev with
  | zero =>
    intro acc res h_acc h_some c hc
    change (strictNat (getLaneNat condV 0) fun n =>
      @Bool.rec (fun _ => Option (List (Nat × Nat))) none
        (some ((n, getLaneNat condM 0) :: acc))
        (Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg))) = some res at h_some
    rw [strictNat_eq] at h_some
    let n := getLaneNat condV 0
    cases h_b : (Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg)) with
    | false =>
      rw [h_b] at h_some; contradiction
    | true =>
      rw [h_b] at h_some
      dsimp only at h_some
      injection h_some with h_eq
      subst h_eq
      rcases List.mem_cons.mp hc with rfl | hc_acc
      · rcases Bool.and_eq_true_iff.mp h_b with ⟨hb1, hb2⟩
        exact ⟨Nat.le_of_ble_eq_true hb1, Nat.le_of_ble_eq_true hb2⟩
      · exact h_acc c hc_acc
  | succ i ih =>
    intro acc res h_acc h_some
    unfold extractCondsLoop at h_some
    dsimp only at h_some
    rw [strictNat_eq, strictNat_eq] at h_some
    let idx := Nat.add i 1
    let n := getLaneNat condV idx
    change (@Bool.rec (fun _ => Option (List (Nat × Nat))) none
      (extractCondsLoop deg condV condM i ((n, getLaneNat condM idx) :: acc))
      (Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg))) = some res at h_some
    cases h_b : (Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg)) with
    | false =>
      rw [h_b] at h_some; contradiction
    | true =>
      rw [h_b] at h_some
      dsimp only at h_some
      apply ih ((n, getLaneNat condM idx) :: acc) res _ h_some
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc_acc
      · rcases Bool.and_eq_true_iff.mp h_b with ⟨hb1, hb2⟩
        exact ⟨Nat.le_of_ble_eq_true hb1, Nat.le_of_ble_eq_true hb2⟩
      · exact h_acc c hc_acc

theorem extractCondsRec_sound (deg condV condM lev : Nat) {conds : List (Nat × Nat)}
    (h_some : extractCondsRec deg condV condM lev = some conds) :
    ∀ c ∈ conds, 1 ≤ c.1 ∧ c.1 ≤ 2 * deg := by
  rw [extractCondsRec_eq_loop] at h_some
  exact extractCondsLoop_sound deg condV condM lev [] conds (fun _ h => by cases h) h_some

theorem findSymOutletRec_mem (line : Nat) (syms : List SymOutlet) {found : SymOutlet}
    (h_find : findSymOutletRec line syms = some found) :
    found ∈ syms := by
  induction syms with
  | nil =>
    unfold findSymOutletRec at h_find
    contradiction
  | cons o syms ih =>
    unfold findSymOutletRec at h_find
    dsimp only at h_find
    change (@Bool.rec (fun _ => Option SymOutlet) (findSymOutletRec line syms) (some o) (Nat.beq o.number line)) = some found at h_find
    cases h_eq : Nat.beq o.number line with
    | true =>
      rw [h_eq] at h_find
      dsimp only at h_find
      injection h_find with h_o
      subst h_o
      exact List.mem_cons_self
    | false =>
      rw [h_eq] at h_find
      dsimp only at h_find
      exact List.mem_cons_of_mem _ (ih h_find)

/-!
### Stage L.1: Real Hypermap Cartwheel Instantiation (`spokeDart`, `cartDart`, `cartDegOfDart`, `dischargingTreesVerified_hypermap_soundness`)
-/

/-- The `i`-th outgoing spoke dart (`1 ≤ i ≤ deg`) around hub dart `d0` in hypermap `H`,
    obtained by iterating `H.node.f` `(i - 1)` times starting from `d0`. -/
def spokeDart (H : Hypermap) (d0 : H.Dart) (i : Nat) : H.Dart :=
  Hypermap.Perm.iter H.node (i - 1) d0

@[simp] theorem spokeDart_one (H : Hypermap) (d0 : H.Dart) :
    spokeDart H d0 1 = d0 := rfl

theorem spokeDart_succ (H : Hypermap) (d0 : H.Dart) {i : Nat} (hi : 1 ≤ i) :
    spokeDart H d0 (i + 1) = H.node.f (spokeDart H d0 i) := by
  cases i with
  | zero => omega
  | succ k => rfl

theorem perm_iter_mem_getOrbit_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (d0 : H.Dart) (n : Nat) :
    Hypermap.Perm.iter H.node n d0 ∈ getOrbit H.node fuel d0 := by
  induction n with
  | zero =>
    exact List.contains_iff_mem.mp (Hypermap.getOrbit_contains_self H.node fuel d0)
  | succ n ih =>
    rw [Hypermap.Perm.iter_succ]
    exact Hypermap.getOrbit_closed_under_f_of_complete H.node darts h_all h_le ih

/-- Every `spokeDart H d0 i` belongs to the node orbit `getOrbit H.node fuel d0` on a complete dart list. -/
theorem spokeDart_mem_getOrbit_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (d0 : H.Dart) (i : Nat) :
    spokeDart H d0 i ∈ getOrbit H.node fuel d0 :=
  perm_iter_mem_getOrbit_of_complete H darts h_all h_le d0 (i - 1)

/-- Maps each RSST cartwheel position `0 ≤ p ≤ 5 * deg` around hub dart `d0` in hypermap `H`
    to its representative vertex dart, matching the 5 concentric cartwheel rings of `getAdjMat` / `doFan` / `doOutlet`:
    - `p = 0`: hub dart `d0`
    - `1 ≤ p ≤ deg` (`ringIdx = 0`, spoke `i`): `ruleVertexDart H true (H.edge.f s_i) 0` (`= H.edge.f s_i`)
    - `deg + 1 ≤ p ≤ 2 * deg` (`ringIdx = 1`, hat `deg + i`): `ruleVertexDart H true (H.edge.f s_i) 5`
    - `2 * deg + 1 ≤ p ≤ 3 * deg` (`ringIdx = 2`, 1st fan `2 * deg + i`): `ruleVertexDart H true (H.edge.f s_i) 12`
    - `3 * deg + 1 ≤ p ≤ 4 * deg` (`ringIdx = 3`, 2nd fan `3 * deg + i`): `ruleVertexDart H true (H.edge.f s_i) 13`
    - `4 * deg + 1 ≤ p ≤ 5 * deg` (`ringIdx ≥ 4`, 3rd fan `4 * deg + i`): `H.edge.f (H.node.f^5 (H.edge.f s_i))`. -/
def cartDart (H : Hypermap) (deg : Nat) (d0 : H.Dart) (p : Nat) : H.Dart :=
  if p == 0 then d0
  else
    let ringIdx := (p - 1) / deg
    let s := spokeDart H d0 ((p - 1) % deg + 1)
    if ringIdx == 0 then ruleVertexDart H true (H.edge.f s) 0
    else if ringIdx == 1 then ruleVertexDart H true (H.edge.f s) 5
    else if ringIdx == 2 then ruleVertexDart H true (H.edge.f s) 12
    else if ringIdx == 3 then ruleVertexDart H true (H.edge.f s) 13
    else H.edge.f (H.node.f (H.node.f (H.node.f (H.node.f (H.node.f (H.edge.f s))))))

/-- Concrete cartwheel degree assignment `Nat → Nat` around hub dart `d0` in hypermap `H`. -/
def cartDegOfDart (H : Hypermap) [DecidableEq H.Dart] (fuel deg : Nat) (d0 : H.Dart) (p : Nat) : Nat :=
  Hypermap.nodeDegree H (cartDart H deg d0 p) fuel

@[simp] theorem cartDart_zero (H : Hypermap) (deg : Nat) (d0 : H.Dart) :
    cartDart H deg d0 0 = d0 := rfl

@[simp] theorem cartDegOfDart_zero (H : Hypermap) [DecidableEq H.Dart] (fuel deg : Nat) (d0 : H.Dart) :
    cartDegOfDart H fuel deg d0 0 = Hypermap.nodeDegree H d0 fuel := rfl

theorem ringIdx_of_mul_add {deg k i : Nat} (hi1 : 1 ≤ i) (hi2 : i ≤ deg) :
    ((k * deg + i) - 1) / deg = k := by
  have h_deg_pos : 0 < deg := by omega
  have h_eq : (k * deg + i) - 1 = (i - 1) + deg * k := by
    rw [Nat.mul_comm deg k]
    omega
  rw [h_eq, Nat.add_mul_div_left (i - 1) k h_deg_pos, Nat.div_eq_of_lt (by omega), Nat.zero_add]

theorem spokeIdx_of_mul_add {deg k i : Nat} (hi1 : 1 ≤ i) (hi2 : i ≤ deg) :
    ((k * deg + i) - 1) % deg + 1 = i := by
  have h_eq : (k * deg + i) - 1 = (i - 1) + deg * k := by
    rw [Nat.mul_comm deg k]
    omega
  rw [h_eq, Nat.add_mul_mod_self_left (i - 1) deg k, Nat.mod_eq_of_lt (by omega)]
  omega

/-- For `1 ≤ i ≤ deg`, cartwheel spoke position `i` maps to `H.edge.f (spokeDart H d0 i)`. -/
theorem cartDart_spoke (H : Hypermap) (deg : Nat) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi2 : i ≤ deg) :
    cartDart H deg d0 i = H.edge.f (spokeDart H d0 i) := by
  dsimp [cartDart]
  have h_ne0 : (i == 0) = false := beq_false_of_ne (by omega)
  have h_div : (i - 1) / deg = 0 := by
    simpa using ringIdx_of_mul_add (k := 0) hi1 hi2
  have h_mod : (i - 1) % deg + 1 = i := by
    simpa using spokeIdx_of_mul_add (k := 0) hi1 hi2
  rw [h_ne0, h_div, h_mod]
  rfl

/-- For `1 ≤ i ≤ deg`, cartwheel hat position `deg + i` maps to `ruleVertexDart H true (H.edge.f (spokeDart H d0 i)) 5`. -/
theorem cartDart_hat (H : Hypermap) (deg : Nat) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi2 : i ≤ deg) :
    cartDart H deg d0 (deg + i) = ruleVertexDart H true (H.edge.f (spokeDart H d0 i)) 5 := by
  dsimp [cartDart]
  have h_ne0 : (deg + i == 0) = false := beq_false_of_ne (by omega)
  have h_div : ((deg + i) - 1) / deg = 1 := by
    simpa using ringIdx_of_mul_add (k := 1) hi1 hi2
  have h_mod : ((deg + i) - 1) % deg + 1 = i := by
    simpa using spokeIdx_of_mul_add (k := 1) hi1 hi2
  rw [h_ne0, h_div, h_mod]
  rfl

/-- For `1 ≤ i ≤ deg`, 1st fan position `2 * deg + i` maps to `ruleVertexDart H true (H.edge.f (spokeDart H d0 i)) 12`. -/
theorem cartDart_fan1 (H : Hypermap) (deg : Nat) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi2 : i ≤ deg) :
    cartDart H deg d0 (2 * deg + i) = ruleVertexDart H true (H.edge.f (spokeDart H d0 i)) 12 := by
  dsimp [cartDart]
  have h_ne0 : (2 * deg + i == 0) = false := beq_false_of_ne (by omega)
  have h_div : ((2 * deg + i) - 1) / deg = 2 := ringIdx_of_mul_add (k := 2) hi1 hi2
  have h_mod : ((2 * deg + i) - 1) % deg + 1 = i := spokeIdx_of_mul_add (k := 2) hi1 hi2
  rw [h_ne0, h_div, h_mod]
  rfl

/-- For `1 ≤ i ≤ deg`, 2nd fan position `3 * deg + i` maps to `ruleVertexDart H true (H.edge.f (spokeDart H d0 i)) 13`. -/
theorem cartDart_fan2 (H : Hypermap) (deg : Nat) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi2 : i ≤ deg) :
    cartDart H deg d0 (3 * deg + i) = ruleVertexDart H true (H.edge.f (spokeDart H d0 i)) 13 := by
  dsimp [cartDart]
  have h_ne0 : (3 * deg + i == 0) = false := beq_false_of_ne (by omega)
  have h_div : ((3 * deg + i) - 1) / deg = 3 := ringIdx_of_mul_add (k := 3) hi1 hi2
  have h_mod : ((3 * deg + i) - 1) % deg + 1 = i := spokeIdx_of_mul_add (k := 3) hi1 hi2
  rw [h_ne0, h_div, h_mod]
  rfl

/-- For `1 ≤ i ≤ deg`, 3rd fan position `4 * deg + i` maps to `H.edge.f (H.node.f^5 (H.edge.f (spokeDart H d0 i)))`. -/
theorem cartDart_fan3 (H : Hypermap) (deg : Nat) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi2 : i ≤ deg) :
    cartDart H deg d0 (4 * deg + i) =
      H.edge.f (H.node.f (H.node.f (H.node.f (H.node.f (H.node.f (H.edge.f (spokeDart H d0 i))))))) := by
  dsimp [cartDart]
  have h_ne0 : (4 * deg + i == 0) = false := beq_false_of_ne (by omega)
  have h_div : ((4 * deg + i) - 1) / deg = 4 := ringIdx_of_mul_add (k := 4) hi1 hi2
  have h_mod : ((4 * deg + i) - 1) % deg + 1 = i := spokeIdx_of_mul_add (k := 4) hi1 hi2
  rw [h_ne0, h_div, h_mod]
  rfl

/-!
### Stage L.2: Degree-6 Discharging with Degree-5 and Degree-6 Neighbors (Primal & Dual)
-/

/-- If `r.b1.1 > degs 1` (`0 < r.b1.1`), then `matchesRawRuleDegs degs r = false`. -/
theorem not_matchesRawRuleDegs_of_b1_lt (degs : Nat → Nat) (r : RawRule)
    (h_pos : 0 < r.b1.1) (h_lt : degs 1 < r.b1.1) :
    matchesRawRuleDegs degs r = false := by
  dsimp [matchesRawRuleDegs]
  rw [@degMatchesBound_eq_false_of_lt (degs 1) r.b1 h_pos h_lt]
  simp

/-- When `degs 0 = 5` and `degs 1 ≤ 6`, rule `r3` (`b1 = (7, 12)`) vanishes,
    so at most `r1` and `r5` can match (`orientOutflowDegs inv degs ≤ 2`). -/
theorem orientOutflowDegs_le_2_of_deg_5_of_target_deg_le_6 (inv : Bool) (degs : Nat → Nat)
    (hb0 : degs 0 = 5) (hb1 : degs 1 ≤ 6) :
    orientOutflowDegs inv degs ≤ 2 := by
  rw [orientOutflowDegs_eq_filter_active inv degs 5 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 5 0) = [r1, r3, r5] := rfl
  rw [h_filt]; dsimp only [List.foldl]
  have h3 : matchesRawRuleDegs degs r3 = false :=
    not_matchesRawRuleDegs_of_b1_lt degs r3 (by decide) (by dsimp [r3]; omega)
  have h1 : (if (if inv then r1.invert else true) && matchesRawRuleDegs degs r1 then (1 : Int) else 0) ≤ 1 := by split <;> omega
  have h5 : (if (if inv then r5.invert else true) && matchesRawRuleDegs degs r5 then (1 : Int) else 0) ≤ 1 := by split <;> omega
  rw [h3]; simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- When `degs 0 = 5` and `7 ≤ degs 3`, both `r3` (`degs 3 = 5`) and `r5` (`degs 3 ≤ 6`) vanish,
    leaving only `r1` (`orientOutflowDegs inv degs ≤ 1`). -/
theorem orientOutflowDegs_le_1_of_deg_5_of_deg3_ge_7 (inv : Bool) (degs : Nat → Nat)
    (hb0 : degs 0 = 5) (hb3 : 7 ≤ degs 3) :
    orientOutflowDegs inv degs ≤ 1 := by
  rw [orientOutflowDegs_eq_filter_active inv degs 5 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 5 0) = [r1, r3, r5] := rfl
  rw [h_filt]; dsimp only [List.foldl]
  have h3 : matchesRawRuleDegs degs r3 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r3 3 5 5 (by decide) (by decide) (by omega)
  have h5 : matchesRawRuleDegs degs r5 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r5 3 5 6 (by decide) (by decide) (by omega)
  have h1 : (if (if inv then r1.invert else true) && matchesRawRuleDegs degs r1 then (1 : Int) else 0) ≤ 1 := by split <;> omega
  rw [h3, h5]; simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- When `degs 0 = 6` and `degs 1 ≤ 6`, rules `r3, r13, r15` (`b1 = (7, 12)`) vanish
    and `{r5, r11}` / `{r7, r9}` conflict, so `orientOutflowDegs inv degs ≤ 2`. -/
theorem orientOutflowDegs_le_2_of_deg_6_of_target_deg_le_6 (inv : Bool) (degs : Nat → Nat)
    (hb0 : degs 0 = 6) (hb1 : degs 1 ≤ 6) :
    orientOutflowDegs inv degs ≤ 2 := by
  rw [orientOutflowDegs_eq_filter_active inv degs 6 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 6 0) = [r3, r5, r7, r9, r11, r13, r15] := rfl
  rw [h_filt]; dsimp only [List.foldl]
  have h3 : matchesRawRuleDegs degs r3 = false :=
    not_matchesRawRuleDegs_of_b1_lt degs r3 (by decide) (by dsimp [r3]; omega)
  have h13 : matchesRawRuleDegs degs r13 = false :=
    not_matchesRawRuleDegs_of_b1_lt degs r13 (by decide) (by dsimp [r13]; omega)
  have h15 : matchesRawRuleDegs degs r15 = false :=
    not_matchesRawRuleDegs_of_b1_lt degs r15 (by decide) (by dsimp [r15]; omega)
  have hc5_11 := conflict_pair_at inv degs r5 r11 5 5 5 6 6 (by decide) (by decide) (by decide) (by decide)
  have hc7_9 := conflict_pair_at inv degs r7 r9 3 5 5 6 6 (by decide) (by decide) (by decide) (by decide)
  rw [h3, h13, h15]; simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- When `degs 0 = 6` and `7 ≤ degs 3`, all 7 rules `r3..r15` vanish (`orientOutflowDegs inv degs = 0`). -/
theorem orientOutflowDegs_eq_zero_of_deg_6_of_deg3_ge_7 (inv : Bool) (degs : Nat → Nat)
    (hb0 : degs 0 = 6) (hb3 : 7 ≤ degs 3) :
    orientOutflowDegs inv degs = 0 := by
  rw [orientOutflowDegs_eq_filter_active inv degs 6 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 6 0) = [r3, r5, r7, r9, r11, r13, r15] := rfl
  rw [h_filt]; dsimp only [List.foldl]
  have h3 : matchesRawRuleDegs degs r3 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r3 3 5 5 (by decide) (by decide) (by omega)
  have h5 : matchesRawRuleDegs degs r5 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r5 3 5 6 (by decide) (by decide) (by omega)
  have h7 : matchesRawRuleDegs degs r7 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r7 3 5 5 (by decide) (by decide) (by omega)
  have h9 : matchesRawRuleDegs degs r9 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r9 3 6 6 (by decide) (by decide) (by omega)
  have h11 : matchesRawRuleDegs degs r11 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r11 3 6 6 (by decide) (by decide) (by omega)
  have h13 : matchesRawRuleDegs degs r13 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r13 3 5 5 (by decide) (by decide) (by omega)
  have h15 : matchesRawRuleDegs degs r15 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r15 3 6 6 (by decide) (by decide) (by omega)
  rw [h3, h5, h7, h9, h11, h13, h15]; simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- When `degs 0 = 6`, `degs 1 ≤ 6`, `6 ≤ degs 5`, `6 ≤ degs 9`, and `6 ≤ degs 11`,
    every rule in `theRules` vanishes (`orientOutflowDegs inv degs = 0`). -/
theorem orientOutflowDegs_eq_zero_of_deg_6_of_target_deg_le_6_of_no_deg5_second_ring
    (inv : Bool) (degs : Nat → Nat)
    (hb0 : degs 0 = 6) (hb1 : degs 1 ≤ 6)
    (hb5 : 6 ≤ degs 5) (hb9 : 6 ≤ degs 9) (hb11 : 6 ≤ degs 11) :
    orientOutflowDegs inv degs = 0 := by
  rw [orientOutflowDegs_eq_filter_active inv degs 6 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 6 0) = [r3, r5, r7, r9, r11, r13, r15] := rfl
  rw [h_filt]; dsimp only [List.foldl]
  have h3 : matchesRawRuleDegs degs r3 = false :=
    not_matchesRawRuleDegs_of_b1_lt degs r3 (by decide) (by dsimp [r3]; omega)
  have h5 : matchesRawRuleDegs degs r5 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r5 5 5 5 (by decide) (by decide) (by omega)
  have h7 : matchesRawRuleDegs degs r7 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r7 9 5 5 (by decide) (by decide) (by omega)
  have h9 : matchesRawRuleDegs degs r9 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r9 9 5 5 (by decide) (by decide) (by omega)
  have h11 : matchesRawRuleDegs degs r11 = false :=
    not_matchesRawRuleDegs_of_triple_gt degs r11 11 5 5 (by decide) (by decide) (by omega)
  have h13 : matchesRawRuleDegs degs r13 = false :=
    not_matchesRawRuleDegs_of_b1_lt degs r13 (by decide) (by dsimp [r13]; omega)
  have h15 : matchesRawRuleDegs degs r15 = false :=
    not_matchesRawRuleDegs_of_b1_lt degs r15 (by decide) (by dsimp [r15]; omega)
  rw [h3, h5, h7, h9, h11, h13, h15]; simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- Compensating Outflow Lemma for Degree-6 Vertices (`r3` activation):
    when `degs 0 = 6`, `7 ≤ degs 1`, and `degs 3 = 5`, rule `r3` fires in orientation `inv`,
    so `1 ≤ orientOutflowDegs inv degs`. -/
theorem one_le_orientOutflowDegs_of_deg_6_of_target_deg_ge_7_of_deg3_5 (inv : Bool) (degs : Nat → Nat)
    (hb0 : degs 0 = 6) (hb1 : 7 ≤ degs 1) (hb3 : degs 3 = 5) :
    1 ≤ orientOutflowDegs inv degs := by
  rw [orientOutflowDegs_eq_filter_active inv degs 6 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 6 0) = [r3, r5, r7, r9, r11, r13, r15] := rfl
  rw [h_filt]; dsimp only [List.foldl]
  have hr3 : matchesRawRuleDegs degs r3 = true := by
    dsimp [matchesRawRuleDegs, r3, List.all, degMatchesBound]
    rw [hb0, hb3, decide_eq_true hb1]
    rfl
  have h_inv3 : (if inv then r3.invert else true) = true := by cases inv <;> rfl
  have h5 : 0 ≤ (if (if inv then r5.invert else true) && matchesRawRuleDegs degs r5 then (1 : Int) else 0) := by split <;> omega
  have h7 : 0 ≤ (if (if inv then r7.invert else true) && matchesRawRuleDegs degs r7 then (1 : Int) else 0) := by split <;> omega
  have h9 : 0 ≤ (if (if inv then r9.invert else true) && matchesRawRuleDegs degs r9 then (1 : Int) else 0) := by split <;> omega
  have h11 : 0 ≤ (if (if inv then r11.invert else true) && matchesRawRuleDegs degs r11 then (1 : Int) else 0) := by split <;> omega
  have h13 : 0 ≤ (if (if inv then r13.invert else true) && matchesRawRuleDegs degs r13 then (1 : Int) else 0) := by split <;> omega
  have h15 : 0 ≤ (if (if inv then r15.invert else true) && matchesRawRuleDegs degs r15 then (1 : Int) else 0) := by split <;> omega
  rw [hr3, h_inv3]; dsimp; omega

/-- Double Compensating Outflow Lemma for Degree-6 Vertices (`r3 + r5` activation):
    when `degs 0 = 6`, `7 ≤ degs 1`, `degs 3 = 5`, and `degs 5 = 5`, both `r3` and `r5` fire
    in orientation `inv`, so `2 ≤ orientOutflowDegs inv degs`. -/
theorem two_le_orientOutflowDegs_of_deg_6_of_target_deg_ge_7_of_deg3_5_of_deg5_5 (inv : Bool) (degs : Nat → Nat)
    (hb0 : degs 0 = 6) (hb1 : 7 ≤ degs 1) (hb3 : degs 3 = 5) (hb5 : degs 5 = 5) :
    2 ≤ orientOutflowDegs inv degs := by
  rw [orientOutflowDegs_eq_filter_active inv degs 6 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 6 0) = [r3, r5, r7, r9, r11, r13, r15] := rfl
  rw [h_filt]; dsimp only [List.foldl]
  have hr3 : matchesRawRuleDegs degs r3 = true := by
    dsimp [matchesRawRuleDegs, r3, List.all, degMatchesBound]
    rw [hb0, hb3, decide_eq_true hb1]
    rfl
  have hr5 : matchesRawRuleDegs degs r5 = true := by
    dsimp [matchesRawRuleDegs, r5, List.all, degMatchesBound]
    rw [hb0, hb3, hb5, decide_eq_true (by omega : 6 ≤ degs 1)]
    rfl
  have h_inv3 : (if inv then r3.invert else true) = true := by cases inv <;> rfl
  have h_inv5 : (if inv then r5.invert else true) = true := by cases inv <;> rfl
  have h7 : 0 ≤ (if (if inv then r7.invert else true) && matchesRawRuleDegs degs r7 then (1 : Int) else 0) := by split <;> omega
  have h9 : 0 ≤ (if (if inv then r9.invert else true) && matchesRawRuleDegs degs r9 then (1 : Int) else 0) := by split <;> omega
  have h11 : 0 ≤ (if (if inv then r11.invert else true) && matchesRawRuleDegs degs r11 then (1 : Int) else 0) := by split <;> omega
  have h13 : 0 ≤ (if (if inv then r13.invert else true) && matchesRawRuleDegs degs r13 then (1 : Int) else 0) := by split <;> omega
  have h15 : 0 ≤ (if (if inv then r15.invert else true) && matchesRawRuleDegs degs r15 then (1 : Int) else 0) := by split <;> omega
  rw [hr3, hr5, h_inv3, h_inv5]; dsimp; omega

/-- When a spoke `d` at a degree-6 vertex points to a neighbor `H.edge.f d` of degree `≥ 7`
    and at least one flanking spoke around `H.edge.f d` (`H.node.f (H.edge.f d)` or `H.node.inv (H.edge.f d)`)
    has a degree-5 neighbor, rule `r3` fires from `d` (`1 ≤ dartRuleOutflow H fuel d`). -/
theorem one_le_dartRuleOutflow_of_deg_6_of_target_deg_ge_7_of_flanking_spoke_deg_5
    (H : Hypermap) [DecidableEq H.Dart] (fuel : Nat) (d : H.Dart)
    (h_d6 : Hypermap.nodeDegree H d fuel = 6)
    (h_ed7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel)
    (h_flank5 : Hypermap.nodeDegree H (H.edge.f (H.node.f (H.edge.f d))) fuel = 5 ∨
                Hypermap.nodeDegree H (H.edge.f (H.node.inv (H.edge.f d))) fuel = 5) :
    1 ≤ dartRuleOutflow H fuel d := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  rcases h_flank5 with h_next5 | h_prev5
  · have hf : 0 ≤ orientOutflowDegs false (fun k => Hypermap.nodeDegree H (ruleVertexDart H false d k) fuel) :=
      foldl_add_nonneg _ _ (fun _ _ => by split <;> omega)
    have ht : 1 ≤ orientOutflowDegs true (fun k => Hypermap.nodeDegree H (ruleVertexDart H true d k) fuel) :=
      one_le_orientOutflowDegs_of_deg_6_of_target_deg_ge_7_of_deg3_5 true
        (fun k => Hypermap.nodeDegree H (ruleVertexDart H true d k) fuel)
        (by simpa [ruleVertexDart] using h_d6)
        (by simpa [ruleVertexDart] using h_ed7)
        (by simpa [ruleVertexDart, ruleRotInv] using h_next5)
    omega
  · have hf : 1 ≤ orientOutflowDegs false (fun k => Hypermap.nodeDegree H (ruleVertexDart H false d k) fuel) :=
      one_le_orientOutflowDegs_of_deg_6_of_target_deg_ge_7_of_deg3_5 false
        (fun k => Hypermap.nodeDegree H (ruleVertexDart H false d k) fuel)
        (by simpa [ruleVertexDart] using h_d6)
        (by simpa [ruleVertexDart] using h_ed7)
        (by simpa [ruleVertexDart, ruleRotInv] using h_prev5)
    have ht : 0 ≤ orientOutflowDegs true (fun k => Hypermap.nodeDegree H (ruleVertexDart H true d k) fuel) :=
      foldl_add_nonneg _ _ (fun _ _ => by split <;> omega)
    omega

/-- When a spoke `d` at a degree-6 vertex points to a neighbor `H.edge.f d` of degree `≥ 7`
    and BOTH flanking spokes `H.node.f (H.edge.f d)` and `H.node.inv (H.edge.f d)` have degree-5 neighbors,
    rule `r3` fires in both orientations (`2 ≤ dartRuleOutflow H fuel d`). -/
theorem two_le_dartRuleOutflow_of_deg_6_of_target_deg_ge_7_of_both_flanking_spokes_deg_5
    (H : Hypermap) [DecidableEq H.Dart] (fuel : Nat) (d : H.Dart)
    (h_d6 : Hypermap.nodeDegree H d fuel = 6)
    (h_ed7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel)
    (h_next5 : Hypermap.nodeDegree H (H.edge.f (H.node.f (H.edge.f d))) fuel = 5)
    (h_prev5 : Hypermap.nodeDegree H (H.edge.f (H.node.inv (H.edge.f d))) fuel = 5) :
    2 ≤ dartRuleOutflow H fuel d := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have hf : 1 ≤ orientOutflowDegs false (fun k => Hypermap.nodeDegree H (ruleVertexDart H false d k) fuel) :=
    one_le_orientOutflowDegs_of_deg_6_of_target_deg_ge_7_of_deg3_5 false
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H false d k) fuel)
      (by simpa [ruleVertexDart] using h_d6)
      (by simpa [ruleVertexDart] using h_ed7)
      (by simpa [ruleVertexDart, ruleRotInv] using h_prev5)
  have ht : 1 ≤ orientOutflowDegs true (fun k => Hypermap.nodeDegree H (ruleVertexDart H true d k) fuel) :=
    one_le_orientOutflowDegs_of_deg_6_of_target_deg_ge_7_of_deg3_5 true
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H true d k) fuel)
      (by simpa [ruleVertexDart] using h_d6)
      (by simpa [ruleVertexDart] using h_ed7)
      (by simpa [ruleVertexDart, ruleRotInv] using h_next5)
  omega

/-- Global Degree-6 Discharging Theorem with Degree-`≥ 6` Neighbors:
    if `nodeDegree H u fuel = 6` and every spoke `d ∈ getOrbit H.node fuel u` has
    either `7 ≤ nodeDegree H (H.edge.f d) fuel` or flanking spokes of degree `≥ 7`
    (`7 ≤ nodeDegree H (H.edge.f (H.node.f d)) fuel ∧ 7 ≤ nodeDegree H (H.edge.f (H.node.inv d)) fuel`,
    with `6 ≤ nodeDegree H (H.edge.f d) fuel`),
    then `finalCharge H (rsstChargeShift H fuel) darts u ≤ 0`. -/
theorem finalCharge_le_zero_of_deg_6_of_neighbors_deg_ge_6_of_flanking_spokes_ge_7
    (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (h_deg6 : Hypermap.nodeDegree H u fuel = 6)
    (h_nb6 : ∀ d ∈ getOrbit H.node fuel u, 6 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel)
    (h_flank7 : ∀ d ∈ getOrbit H.node fuel u,
      7 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel ∨
      (7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel ∧
       7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel)) :
    finalCharge H (rsstChargeShift H fuel) darts u ≤ 0 := by
  apply finalCharge_le_zero_of_deg_6_of_orbitNetShift_nonpos H darts h_all h_le u h_loopless h_deg6
  dsimp [orbitNetShift]
  have h_le_c := foldl_add_le_of_le_const (getOrbit H.node fuel u) (fun d => netDartShift H fuel d) 0 (by
    intro d hd
    dsimp only
    have hd_deg : Hypermap.nodeDegree H d fuel ≤ 6 := by
      have := nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hd
      omega
    have h_out_nonneg : 0 ≤ dartRuleOutflow H fuel d := dartRuleOutflow_nonneg H fuel d
    rcases h_flank7 d hd with h_ed7 | ⟨h_next7, h_prev7⟩
    · rw [netDartShift_eq_neg_outflow_of_deg_le_6_of_target_deg_ge_7 H fuel d (H.edge_involution d) hd_deg h_ed7]
      omega
    · dsimp [netDartShift]
      have h_in0 : dartRuleOutflow H fuel (H.edge.f d) = 0 :=
        dartRuleOutflow_eq_zero_of_deg_ge_6_of_flanking_spokes_ge_7 H fuel d (h_nb6 d hd) h_next7 h_prev7
      omega)
  dsimp at h_le_c
  omega

/-- Primal–Dual Degree-6 Discharging Theorem on `H.dual` with Degree-`≥ 6` Neighbors. -/
theorem dual_finalCharge_le_zero_of_deg_6_of_isBridgeless_of_neighbors_deg_ge_6_of_flanking_spokes_ge_7
    (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b fuel : Nat} (h_le_b : darts.length ≤ fuel_b) (h_le : darts.length ≤ fuel)
    (h_bridge : Hypermap.isBridgeless H darts fuel_b) (u : H.Dart)
    (h_deg6 : Hypermap.nodeDegree H.dual u fuel = 6)
    (h_nb6 : ∀ d ∈ getOrbit H.dual.node fuel u, 6 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f d) fuel)
    (h_flank7 : ∀ d ∈ getOrbit H.dual.node fuel u,
      7 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f d) fuel ∨
      (7 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f (H.dual.node.f d)) fuel ∧
       7 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f (H.dual.node.inv d)) fuel)) :
    finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0 := by
  have h_loopless : ∀ d ∈ getOrbit H.dual.node fuel u, Hypermap.sameVertex H.dual (H.dual.edge.f d) u fuel = false :=
    dual_loopless_orbit_of_isBridgeless H darts h_all h_le_b h_le h_bridge u
  exact finalCharge_le_zero_of_deg_6_of_neighbors_deg_ge_6_of_flanking_spokes_ge_7
    H.dual darts h_all h_le u h_loopless h_deg6 h_nb6 h_flank7

/-!
### Stage L.3: Hub-Cap Discharging Bounds for Degrees 12–19 with Degree-5 Neighbors & Master Phase 5 Synthesis
-/

/-- When `degs 0 = 5` and either `6 ≤ degs 3` or `6 ≤ degs 5`,
    at most 2 of the 3 rules `[r1, r3, r5]` can match (`orientOutflowDegs inv degs ≤ 2`). -/
theorem orientOutflowDegs_le_2_of_deg_5_of_deg3_ge_6_or_deg5_ge_6 (inv : Bool) (degs : Nat → Nat)
    (hb0 : degs 0 = 5) (h_3_or_5 : 6 ≤ degs 3 ∨ 6 ≤ degs 5) :
    orientOutflowDegs inv degs ≤ 2 := by
  rw [orientOutflowDegs_eq_filter_active inv degs 5 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 5 0) = [r1, r3, r5] := rfl
  rw [h_filt]; dsimp only [List.foldl]
  have h1 : (if (if inv then r1.invert else true) && matchesRawRuleDegs degs r1 then (1 : Int) else 0) ≤ 1 := by split <;> omega
  have h3_le : (if (if inv then r3.invert else true) && matchesRawRuleDegs degs r3 then (1 : Int) else 0) ≤ 1 := by split <;> omega
  have h5_le : (if (if inv then r5.invert else true) && matchesRawRuleDegs degs r5 then (1 : Int) else 0) ≤ 1 := by split <;> omega
  rcases h_3_or_5 with hb3 | hb5
  · have h3_zero : matchesRawRuleDegs degs r3 = false :=
      not_matchesRawRuleDegs_of_triple_gt degs r3 3 5 5 (by decide) (by decide) (by omega)
    rw [h3_zero]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
  · have h5_zero : matchesRawRuleDegs degs r5 = false :=
      not_matchesRawRuleDegs_of_triple_gt degs r5 5 5 5 (by decide) (by decide) (by omega)
    rw [h5_zero]; simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- Sharp Incoming Outflow Bound (`≤ 5`) from a Degree-5 Neighbor Flanked on One Side by Degree `≥ 6`:
    if `nodeDegree H (H.edge.f d) fuel = 5` and at least one flanking spoke (`H.node.f d` or `H.node.inv d`)
    has neighbor degree `≥ 6`, then `dartRuleOutflow H fuel (H.edge.f d) ≤ 5`. -/
theorem dartRuleOutflow_le_5_of_deg_5_of_flanking_spoke_ge_6 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_curr5 : Hypermap.nodeDegree H (H.edge.f d) fuel = 5)
    (h_flank6 : 6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel ∨
                6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel) :
    dartRuleOutflow H fuel (H.edge.f d) ≤ 5 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  rcases h_flank6 with h_next6 | h_prev6
  · have hf := orientOutflowDegs_le_3_of_deg_5 false
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
      (by simpa [ruleVertexDart] using h_curr5)
    have ht := orientOutflowDegs_le_2_of_deg_5_of_deg3_ge_6_or_deg5_ge_6 true
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
      (by simpa [ruleVertexDart] using h_curr5)
      (Or.inl (by simpa [ruleVertexDart_true_edge_three] using h_next6))
    omega
  · have hf := orientOutflowDegs_le_2_of_deg_5_of_deg3_ge_6_or_deg5_ge_6 false
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
      (by simpa [ruleVertexDart] using h_curr5)
      (Or.inl (by simpa [ruleVertexDart_false_edge_three] using h_prev6))
    have ht := orientOutflowDegs_le_3_of_deg_5 true
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
      (by simpa [ruleVertexDart] using h_curr5)
    omega

/-- Sharp Incoming Outflow Bound (`≤ 4`) from an Isolated Degree-5 Neighbor
    (flanked on both sides by degree-`≥ 6` spoke neighbors):
    if `nodeDegree H (H.edge.f d) fuel = 5`, `6 ≤ nodeDegree H (H.edge.f (H.node.f d)) fuel`,
    and `6 ≤ nodeDegree H (H.edge.f (H.node.inv d)) fuel`, then `dartRuleOutflow H fuel (H.edge.f d) ≤ 4`. -/
theorem dartRuleOutflow_le_4_of_deg_5_of_flanking_spokes_ge_6 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_curr5 : Hypermap.nodeDegree H (H.edge.f d) fuel = 5)
    (h_next6 : 6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel)
    (h_prev6 : 6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel) :
    dartRuleOutflow H fuel (H.edge.f d) ≤ 4 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have hf := orientOutflowDegs_le_2_of_deg_5_of_deg3_ge_6_or_deg5_ge_6 false
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
    (by simpa [ruleVertexDart] using h_curr5)
    (Or.inl (by simpa [ruleVertexDart_false_edge_three] using h_prev6))
  have ht := orientOutflowDegs_le_2_of_deg_5_of_deg3_ge_6_or_deg5_ge_6 true
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
    (by simpa [ruleVertexDart] using h_curr5)
    (Or.inl (by simpa [ruleVertexDart_true_edge_three] using h_next6))
  omega

/-- Sharp Incoming Outflow Bound (`≤ 2`) from a Degree-5 Neighbor Flanked on Both Sides by Degree `≥ 7`:
    if `nodeDegree H (H.edge.f d) fuel = 5`, `7 ≤ nodeDegree H (H.edge.f (H.node.f d)) fuel`,
    and `7 ≤ nodeDegree H (H.edge.f (H.node.inv d)) fuel`, then `dartRuleOutflow H fuel (H.edge.f d) ≤ 2`. -/
theorem dartRuleOutflow_le_2_of_deg_5_of_flanking_spokes_ge_7 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_curr5 : Hypermap.nodeDegree H (H.edge.f d) fuel = 5)
    (h_next7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel)
    (h_prev7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel) :
    dartRuleOutflow H fuel (H.edge.f d) ≤ 2 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have hf := orientOutflowDegs_le_1_of_deg_5_of_deg3_ge_7 false
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
    (by simpa [ruleVertexDart] using h_curr5)
    (by simpa [ruleVertexDart_false_edge_three] using h_prev7)
  have ht := orientOutflowDegs_le_1_of_deg_5_of_deg3_ge_7 true
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
    (by simpa [ruleVertexDart] using h_curr5)
    (by simpa [ruleVertexDart_true_edge_three] using h_next7)
  omega

/-- Sharp Incoming Outflow Bound (`≤ 3`) from a Degree-6 Neighbor Flanked on One Side by Degree `≥ 7`. -/
theorem dartRuleOutflow_le_3_of_deg_6_of_flanking_spoke_ge_7 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_curr6 : Hypermap.nodeDegree H (H.edge.f d) fuel = 6)
    (h_flank7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel ∨
                7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel) :
    dartRuleOutflow H fuel (H.edge.f d) ≤ 3 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  rcases h_flank7 with h_next7 | h_prev7
  · have hf := orientOutflowDegs_le_3_of_deg_6 false
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
      (by simpa [ruleVertexDart] using h_curr6)
    have ht := orientOutflowDegs_eq_zero_of_deg_6_of_deg3_ge_7 true
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
      (by simpa [ruleVertexDart] using h_curr6)
      (by simpa [ruleVertexDart_true_edge_three] using h_next7)
    omega
  · have hf := orientOutflowDegs_eq_zero_of_deg_6_of_deg3_ge_7 false
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
      (by simpa [ruleVertexDart] using h_curr6)
      (by simpa [ruleVertexDart_false_edge_three] using h_prev7)
    have ht := orientOutflowDegs_le_3_of_deg_6 true
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
      (by simpa [ruleVertexDart] using h_curr6)
    omega

/-- Global Hub-Cap Discharging Theorem for Degrees `12–19` (and all `deg ≥ 12`) with Degree-5 Neighbors:
    for any loopless hub vertex `u` of degree `k ≥ 12` where every spoke `d ∈ getOrbit H.node fuel u`
    either:
    1. points to a degree-5 neighbor with at least one flanking spoke of degree `≥ 6`
       (no 3 consecutive degree-5 neighbors), or
    2. points to a neighbor of degree `≥ 6` flanked by degree-`≥ 6` spokes, or
    3. points to a degree-6 neighbor with at least one flanking spoke of degree `≥ 7`, or
    4. points to a neighbor of degree `≥ 8` (or `< 5`),
    every spoke has `netDartShift H fuel d ≤ 5` and `finalCharge H (rsstChargeShift H fuel) darts u ≤ 0`
    (`60 - 10k + 5k = 60 - 5k ≤ 0` for all `k ≥ 12`). -/
theorem finalCharge_le_zero_of_deg_ge_12_of_deg5_or_deg_ge_6_neighbors
    (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (h_deg12 : 12 ≤ Hypermap.nodeDegree H u fuel)
    (h_spokes : ∀ d ∈ getOrbit H.node fuel u,
      (Hypermap.nodeDegree H (H.edge.f d) fuel = 5 ∧
        (6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel ∨
         6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel)) ∨
      (6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel ∧
       6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel) ∨
      (Hypermap.nodeDegree H (H.edge.f d) fuel = 6 ∧
        (7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel ∨
         7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel)) ∨
      8 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    finalCharge H (rsstChargeShift H fuel) darts u ≤ 0 := by
  rw [finalCharge_eq_initialCharge_add_orbitNetShift H darts h_all h_le u h_loopless]
  dsimp [initialCharge, orbitNetShift]
  have h_le_c := foldl_add_le_of_le_const (getOrbit H.node fuel u) (fun d => netDartShift H fuel d) 5 (by
    intro d hd
    dsimp [netDartShift]
    have hd_deg : Hypermap.nodeDegree H d fuel = Hypermap.nodeDegree H u fuel :=
      nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hd
    have h_out0 : dartRuleOutflow H fuel d = 0 :=
      dartRuleOutflow_eq_zero_of_deg_ge_9 H fuel d (by omega)
    have h_in5 : dartRuleOutflow H fuel (H.edge.f d) ≤ 5 := by
      rcases h_spokes d hd with ⟨h5, h_fl6⟩ | ⟨h_next6, h_prev6⟩ | ⟨h6, h_fl7⟩ | h_ge8
      · exact dartRuleOutflow_le_5_of_deg_5_of_flanking_spoke_ge_6 H fuel d h5 h_fl6
      · exact dartRuleOutflow_le_5_of_target_deg_ge_8_of_flanking_spokes_ge_6 H fuel d (by omega) h_next6 h_prev6
      · have := dartRuleOutflow_le_3_of_deg_6_of_flanking_spoke_ge_7 H fuel d h6 h_fl7; omega
      · rcases Nat.lt_or_ge 8 (Hypermap.nodeDegree H (H.edge.f d) fuel) with h_ge9 | h_le8
        · have := dartRuleOutflow_eq_zero_of_deg_ge_9 H fuel (H.edge.f d) h_ge9; omega
        · have h_eq8 : Hypermap.nodeDegree H (H.edge.f d) fuel = 8 := by omega
          have := dartRuleOutflow_le_4_of_deg_8 H fuel (H.edge.f d) h_eq8; omega
    omega)
  dsimp at h_le_c
  have h_len : (getOrbit H.node fuel u).length = Hypermap.nodeDegree H u fuel := rfl
  omega

/-- Primal–Dual Hub-Cap Discharging Theorem on `H.dual` for Degrees `12–19` (and `deg ≥ 12`) with Degree-5 Neighbors. -/
theorem dual_finalCharge_le_zero_of_deg_ge_12_of_isBridgeless_of_deg5_or_deg_ge_6_neighbors
    (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b fuel : Nat} (h_le_b : darts.length ≤ fuel_b) (h_le : darts.length ≤ fuel)
    (h_bridge : Hypermap.isBridgeless H darts fuel_b) (u : H.Dart)
    (h_deg12 : 12 ≤ Hypermap.nodeDegree H.dual u fuel)
    (h_spokes : ∀ d ∈ getOrbit H.dual.node fuel u,
      (Hypermap.nodeDegree H.dual (H.dual.edge.f d) fuel = 5 ∧
        (6 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f (H.dual.node.f d)) fuel ∨
         6 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f (H.dual.node.inv d)) fuel)) ∨
      (6 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f (H.dual.node.f d)) fuel ∧
       6 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f (H.dual.node.inv d)) fuel) ∨
      (Hypermap.nodeDegree H.dual (H.dual.edge.f d) fuel = 6 ∧
        (7 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f (H.dual.node.f d)) fuel ∨
         7 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f (H.dual.node.inv d)) fuel)) ∨
      8 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f d) fuel) :
    finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0 := by
  have h_loopless : ∀ d ∈ getOrbit H.dual.node fuel u, Hypermap.sameVertex H.dual (H.dual.edge.f d) u fuel = false :=
    dual_loopless_orbit_of_isBridgeless H darts h_all h_le_b h_le h_bridge u
  exact finalCharge_le_zero_of_deg_ge_12_of_deg5_or_deg_ge_6_neighbors
    H.dual darts h_all h_le u h_loopless h_deg12 h_spokes

/-- Global Hub-Cap Discharging Theorem for Degrees `10–19` (and all `deg ≥ 10`) with Isolated Degree-5 Neighbors:
    for any loopless hub vertex `u` of degree `k ≥ 10` where every spoke `d ∈ getOrbit H.node fuel u`
    either:
    1. points to an isolated degree-5 neighbor (`deg = 5` flanked on both sides by degree-`≥ 6` spokes), or
    2. points to a degree-6 neighbor with at least one flanking spoke of degree `≥ 7`, or
    3. points to a neighbor of degree `≥ 8`,
    every spoke has `netDartShift H fuel d ≤ 4` and `finalCharge H (rsstChargeShift H fuel) darts u ≤ 0`
    (`60 - 10k + 4k = 60 - 6k ≤ 0` for all `k ≥ 10`). -/
theorem finalCharge_le_zero_of_deg_ge_10_of_isolated_deg5_neighbors
    (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (h_deg10 : 10 ≤ Hypermap.nodeDegree H u fuel)
    (h_spokes : ∀ d ∈ getOrbit H.node fuel u,
      (Hypermap.nodeDegree H (H.edge.f d) fuel = 5 ∧
       6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel ∧
       6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel) ∨
      (Hypermap.nodeDegree H (H.edge.f d) fuel = 6 ∧
        (7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel ∨
         7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel)) ∨
      8 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    finalCharge H (rsstChargeShift H fuel) darts u ≤ 0 := by
  rw [finalCharge_eq_initialCharge_add_orbitNetShift H darts h_all h_le u h_loopless]
  dsimp [initialCharge, orbitNetShift]
  have h_le_c := foldl_add_le_of_le_const (getOrbit H.node fuel u) (fun d => netDartShift H fuel d) 4 (by
    intro d hd
    dsimp [netDartShift]
    have hd_deg : Hypermap.nodeDegree H d fuel = Hypermap.nodeDegree H u fuel :=
      nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hd
    have h_out0 : dartRuleOutflow H fuel d = 0 :=
      dartRuleOutflow_eq_zero_of_deg_ge_9 H fuel d (by omega)
    have h_in4 : dartRuleOutflow H fuel (H.edge.f d) ≤ 4 := by
      rcases h_spokes d hd with ⟨h5, h_next6, h_prev6⟩ | ⟨h6, h_fl7⟩ | h_ge8
      · exact dartRuleOutflow_le_4_of_deg_5_of_flanking_spokes_ge_6 H fuel d h5 h_next6 h_prev6
      · have := dartRuleOutflow_le_3_of_deg_6_of_flanking_spoke_ge_7 H fuel d h6 h_fl7; omega
      · rcases Nat.lt_or_ge 8 (Hypermap.nodeDegree H (H.edge.f d) fuel) with h_ge9 | h_le8
        · have := dartRuleOutflow_eq_zero_of_deg_ge_9 H fuel (H.edge.f d) h_ge9; omega
        · have h_eq8 : Hypermap.nodeDegree H (H.edge.f d) fuel = 8 := by omega
          exact dartRuleOutflow_le_4_of_deg_8 H fuel (H.edge.f d) h_eq8
    omega)
  dsimp at h_le_c
  have h_len : (getOrbit H.node fuel u).length = Hypermap.nodeDegree H u fuel := rfl
  omega

/-- Primal–Dual Hub-Cap Discharging Theorem on `H.dual` for Degrees `10–19` (and `deg ≥ 10`) with Isolated Degree-5 Neighbors. -/
theorem dual_finalCharge_le_zero_of_deg_ge_10_of_isBridgeless_of_isolated_deg5_neighbors
    (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b fuel : Nat} (h_le_b : darts.length ≤ fuel_b) (h_le : darts.length ≤ fuel)
    (h_bridge : Hypermap.isBridgeless H darts fuel_b) (u : H.Dart)
    (h_deg10 : 10 ≤ Hypermap.nodeDegree H.dual u fuel)
    (h_spokes : ∀ d ∈ getOrbit H.dual.node fuel u,
      (Hypermap.nodeDegree H.dual (H.dual.edge.f d) fuel = 5 ∧
       6 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f (H.dual.node.f d)) fuel ∧
       6 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f (H.dual.node.inv d)) fuel) ∨
      (Hypermap.nodeDegree H.dual (H.dual.edge.f d) fuel = 6 ∧
        (7 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f (H.dual.node.f d)) fuel ∨
         7 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f (H.dual.node.inv d)) fuel)) ∨
      8 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f d) fuel) :
    finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0 := by
  have h_loopless : ∀ d ∈ getOrbit H.dual.node fuel u, Hypermap.sameVertex H.dual (H.dual.edge.f d) u fuel = false :=
    dual_loopless_orbit_of_isBridgeless H darts h_all h_le_b h_le h_bridge u
  exact finalCharge_le_zero_of_deg_ge_10_of_isolated_deg5_neighbors
    H.dual darts h_all h_le u h_loopless h_deg10 h_spokes

/-- Incoming outflow into a degree-`≤ 6` vertex `d` from a degree-`≥ 6` neighbor `H.edge.f d`
    vanishes (`dartRuleOutflow H fuel (H.edge.f d) = 0`) whenever coordinates `5, 9, 11` around `H.edge.f d`
    have degree `≥ 6` in both orientations. -/
theorem dartRuleOutflow_eq_zero_of_deg_ge_6_of_target_deg_le_6_of_no_deg5_second_ring
    (H : Hypermap) [DecidableEq H.Dart] (fuel : Nat) (d : H.Dart)
    (h_d_le6 : Hypermap.nodeDegree H d fuel ≤ 6)
    (h_ed_ge6 : 6 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel)
    (h_sec : ∀ inv : Bool,
      6 ≤ Hypermap.nodeDegree H (ruleVertexDart H inv (H.edge.f d) 5) fuel ∧
      6 ≤ Hypermap.nodeDegree H (ruleVertexDart H inv (H.edge.f d) 9) fuel ∧
      6 ≤ Hypermap.nodeDegree H (ruleVertexDart H inv (H.edge.f d) 11) fuel) :
    dartRuleOutflow H fuel (H.edge.f d) = 0 := by
  rcases Nat.lt_or_ge 6 (Hypermap.nodeDegree H (H.edge.f d) fuel) with h_ge7 | h_le6
  · apply dartRuleOutflow_eq_zero_of_deg_ge_7_of_target_deg_le_6 H fuel (H.edge.f d) h_ge7
    rw [H.edge_involution d]
    exact h_d_le6
  · have h_eq6 : Hypermap.nodeDegree H (H.edge.f d) fuel = 6 := by omega
    rw [dartRuleOutflow_eq_orientOutflowDegs_add]
    rcases h_sec false with ⟨hf5, hf9, hf11⟩
    rcases h_sec true with ⟨ht5, ht9, ht11⟩
    have hf := orientOutflowDegs_eq_zero_of_deg_6_of_target_deg_le_6_of_no_deg5_second_ring false
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
      (by simpa [ruleVertexDart] using h_eq6)
      (by simpa [ruleVertexDart, H.edge_involution] using h_d_le6)
      hf5 hf9 hf11
    have ht := orientOutflowDegs_eq_zero_of_deg_6_of_target_deg_le_6_of_no_deg5_second_ring true
      (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
      (by simpa [ruleVertexDart] using h_eq6)
      (by simpa [ruleVertexDart, H.edge_involution] using h_d_le6)
      ht5 ht9 ht11
    omega

/-- Global Degree-6 Discharging Theorem when all neighbors have degree `≥ 6` and no degree-6 neighbor
    has degree-5 vertices at coordinates `5, 9, 11`. -/
theorem finalCharge_le_zero_of_deg_6_of_neighbors_deg_ge_6_of_no_deg5_second_ring
    (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (h_deg6 : Hypermap.nodeDegree H u fuel = 6)
    (h_nb6 : ∀ d ∈ getOrbit H.node fuel u, 6 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel)
    (h_sec : ∀ d ∈ getOrbit H.node fuel u, ∀ inv : Bool,
      6 ≤ Hypermap.nodeDegree H (ruleVertexDart H inv (H.edge.f d) 5) fuel ∧
      6 ≤ Hypermap.nodeDegree H (ruleVertexDart H inv (H.edge.f d) 9) fuel ∧
      6 ≤ Hypermap.nodeDegree H (ruleVertexDart H inv (H.edge.f d) 11) fuel) :
    finalCharge H (rsstChargeShift H fuel) darts u ≤ 0 := by
  apply finalCharge_le_zero_of_deg_6_of_orbitNetShift_nonpos H darts h_all h_le u h_loopless h_deg6
  dsimp [orbitNetShift]
  have h_le_c := foldl_add_le_of_le_const (getOrbit H.node fuel u) (fun d => netDartShift H fuel d) 0 (by
    intro d hd
    dsimp [netDartShift]
    have hd_deg : Hypermap.nodeDegree H d fuel ≤ 6 := by
      have := nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hd
      omega
    have h_out_nonneg : 0 ≤ dartRuleOutflow H fuel d := dartRuleOutflow_nonneg H fuel d
    have h_in0 : dartRuleOutflow H fuel (H.edge.f d) = 0 :=
      dartRuleOutflow_eq_zero_of_deg_ge_6_of_target_deg_le_6_of_no_deg5_second_ring
        H fuel d hd_deg (h_nb6 d hd) (h_sec d hd)
    omega)
  dsimp at h_le_c
  omega

/-- Primal–Dual Degree-6 Discharging Theorem on `H.dual` when `orbitNetShift H.dual fuel u ≤ 0`
    (covering all degree-6 hubs whose inflow from degree-5/6 neighbors is compensated by outflow to degree-`≥ 7` neighbors). -/
theorem dual_finalCharge_le_zero_of_deg_6_of_isBridgeless_of_orbitNetShift_nonpos
    (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b fuel : Nat} (h_le_b : darts.length ≤ fuel_b) (h_le : darts.length ≤ fuel)
    (h_bridge : Hypermap.isBridgeless H darts fuel_b) (u : H.Dart)
    (h_deg6 : Hypermap.nodeDegree H.dual u fuel = 6)
    (h_net : orbitNetShift H.dual fuel u ≤ 0) :
    finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0 := by
  have h_loopless : ∀ d ∈ getOrbit H.dual.node fuel u, Hypermap.sameVertex H.dual (H.dual.edge.f d) u fuel = false :=
    dual_loopless_orbit_of_isBridgeless H darts h_all h_le_b h_le h_bridge u
  exact finalCharge_le_zero_of_deg_6_of_orbitNetShift_nonpos H.dual darts h_all h_le u h_loopless h_deg6 h_net

/-!
### Stage M.1: `MatchesCartState31` Lifting through `narrowSWAR`, `checkBoundRec`, and `verifyHubcapMembersRec`
-/

/-- Narrowing a 6-bit lane by bitwise AND (`narrowSWAR st po = st &&& po.keep`) preserves `≤ 31`. -/
theorem getLaneNat_narrowSWAR_le_31 {st : Nat} (po : FastPosOut) {p : Nat}
    (h_le : getLaneNat st p ≤ 31) :
    getLaneNat (narrowSWAR st po) p ≤ 31 := by
  change getLaneNat (st &&& po.keep) p ≤ 31
  rw [getLaneNat_and]
  exact Nat.le_trans Nat.and_le_left h_le

/-- Any active well-formed SWAR outlet preserves `MatchesCartState31` under `narrowSWAR`. -/
theorem matchesCartState31_narrowSWAR_of_outletActive (deg : Nat) (cartDeg : Nat → Nat) (st : Nat) (po : FastPosOut)
    (h_deg : deg ≤ 11)
    (h_valid : validFastPosOut deg po = true)
    (h_match31 : MatchesCartState31 deg cartDeg st)
    (h_active : OutletActive deg cartDeg po = true) :
    MatchesCartState31 deg cartDeg (narrowSWAR st po) :=
  ⟨matchesCartState_narrowSWAR_of_outletActive deg cartDeg st po h_deg h_valid h_match31.1 h_active,
   fun p hp1 hp2 => getLaneNat_narrowSWAR_le_31 po (h_match31.2 p hp1 hp2)⟩

/-- `MatchesCartState31` lifting of `checkBoundLoopRec_sound`, collapsing any `reduceAxleRec` call
    directly into `HasExactReducedAxle deg cartDeg`. -/
theorem checkBoundLoopRec_sound31 (deg : Nat) (cartDeg : Nat → Nat) (h_deg : deg ≤ 11)
    (cb : Nat → Nat → List FastPosOut → List FastPosOut → List FastPosOut → Nat → HintStream → Bool × HintStream)
    (h_cb : ∀ (st' forcedIn' : Nat) (negBefore' rem' excluded' : List FastPosOut) (maxch' : Nat) (hs' : HintStream),
      MatchesCartState31 deg cartDeg st' →
      (∀ po ∈ negBefore', validFastPosOut deg po = true ∧ po.isPos = false) →
      (∀ po ∈ rem', validFastPosOut deg po = true) →
      (∀ ex ∈ excluded', OutletActive deg cartDeg ex = false) →
      (cb st' forcedIn' negBefore' rem' excluded' maxch' hs').1 = true →
      HasExactReducedAxle deg cartDeg ∨
      (forcedIn' : Int) + activeOutletSum deg cartDeg negBefore' + activeOutletSum deg cartDeg rem' ≤ (maxch' : Int))
    (st forcedch maxch : Nat) (h_match31 : MatchesCartState31 deg cartDeg st)
    (rem : List FastPosOut) :
    ∀ (allowedch : Nat) (negBefore curExcluded : List FastPosOut) (hs : HintStream),
      allowedch = countPos rem →
      (∀ po ∈ negBefore, validFastPosOut deg po = true ∧ po.isPos = false) →
      (∀ po ∈ rem, validFastPosOut deg po = true) →
      (∀ ex ∈ curExcluded, OutletActive deg cartDeg ex = false) →
      (checkBoundLoopRec cb st forcedch maxch rem allowedch negBefore curExcluded hs).1 = true →
      HasExactReducedAxle deg cartDeg ∨
      (forcedch : Int) + activeOutletSum deg cartDeg negBefore + activeOutletSum deg cartDeg rem ≤ (maxch : Int) := by
  induction rem with
  | nil =>
    intro allowedch negBefore curExcluded hs _ _ _ _ h_ok
    rw [checkBoundLoopRec_nil] at h_ok
    contradiction
  | cons po subRem ih =>
    intro allowedch negBefore curExcluded hs h_all h_neg h_rem h_excl h_ok
    have h_po := h_rem po List.mem_cons_self
    have h_sub : ∀ q ∈ subRem, validFastPosOut deg q = true :=
      fun q hq => h_rem q (List.mem_cons_of_mem po hq)
    rw [checkBoundLoopRec_cons_eq] at h_ok
    simp only [strictNat_eq] at h_ok
    cases h_pos : po.isPos with
    | false =>
      rw [h_pos] at h_ok
      dsimp only at h_ok
      have h_all' : allowedch = countPos subRem := by
        simpa [countPos, h_pos] using h_all
      have h_neg' : ∀ q ∈ po :: negBefore, validFastPosOut deg q = true ∧ q.isPos = false := by
        intro q hq
        rcases List.mem_cons.mp hq with rfl | hq_mem
        · exact ⟨h_po, h_pos⟩
        · exact h_neg q hq_mem
      rcases ih allowedch (po :: negBefore) curExcluded hs h_all' h_neg' h_sub h_excl h_ok with h_red | h_bound
      · exact Or.inl h_red
      · right
        simp only [activeOutletSum] at h_bound ⊢
        omega
    | true =>
      rw [h_pos] at h_ok
      dsimp only at h_ok
      cases h_act : OutletActive deg cartDeg po with
      | true =>
        have h_match_next := matchesCartState31_narrowSWAR_of_outletActive deg cartDeg st po h_deg h_po h_match31 h_act
        have h_no_excl := noExcludedForcedRec_eq_true deg cartDeg (narrowSWAR st po) h_match_next.1 curExcluded h_excl
        rw [h_no_excl] at h_ok
        dsimp only at h_ok
        cases h_cb_ok : (cb (narrowSWAR st po) (Nat.add forcedch 1) negBefore subRem curExcluded maxch hs).fst with
        | false =>
          rw [h_cb_ok] at h_ok; dsimp only at h_ok; contradiction
        | true =>
          rcases h_cb (narrowSWAR st po) (Nat.add forcedch 1) negBefore subRem curExcluded maxch hs
            h_match_next h_neg h_sub h_excl h_cb_ok with h_red | h_bound
          · exact Or.inl h_red
          · right
            simp only [Nat.add_eq, activeOutletSum, outletVal, h_act, h_pos, ↓reduceIte] at h_bound ⊢
            omega
      | false =>
        let resSub :=
          @Bool.rec (fun _ => Bool × HintStream)
            (true, hs)
            (cb (narrowSWAR st po) (Nat.add forcedch 1) negBefore subRem curExcluded maxch hs)
            (noExcludedForcedRec (narrowSWAR st po) curExcluded)
        change (@Bool.rec (fun _ => Bool × HintStream)
          (false, resSub.2)
          (@Bool.rec (fun _ => Bool × HintStream)
            (checkBoundLoopRec cb st forcedch maxch subRem (Nat.sub allowedch 1) negBefore (po :: curExcluded) resSub.2)
            (true, resSub.2)
            (Nat.ble (Nat.add (Nat.sub allowedch 1) forcedch) maxch))
          resSub.1).1 = true at h_ok
        cases h_okSub : resSub.1 with
        | false =>
          rw [h_okSub] at h_ok; dsimp only at h_ok; contradiction
        | true =>
          rw [h_okSub] at h_ok; dsimp only at h_ok
          have h_all' : Nat.sub allowedch 1 = countPos subRem := by
            have : allowedch = 1 + countPos subRem := by simpa [countPos, h_pos] using h_all
            simp only [Nat.sub_eq]
            omega
          cases h_ble : Nat.ble (Nat.add (Nat.sub allowedch 1) forcedch) maxch with
          | true =>
            right
            have h_le : (Nat.sub allowedch 1) + forcedch ≤ maxch := Nat.le_of_ble_eq_true h_ble
            have h_neg_le : activeOutletSum deg cartDeg negBefore ≤ 0 :=
              activeOutletSum_le_zero_of_all_neg deg cartDeg negBefore (fun q hq => (h_neg q hq).2)
            have h_sub_le : activeOutletSum deg cartDeg subRem ≤ (countPos subRem : Int) :=
              activeOutletSum_le_countPos deg cartDeg subRem
            simp only [activeOutletSum, h_act, Bool.false_eq_true, ↓reduceIte]
            omega
          | false =>
            rw [h_ble] at h_ok; dsimp only at h_ok
            have h_excl' : ∀ ex ∈ po :: curExcluded, OutletActive deg cartDeg ex = false := by
              intro ex hex
              rcases List.mem_cons.mp hex with rfl | hex_mem
              · exact h_act
              · exact h_excl ex hex_mem
            rcases ih (Nat.sub allowedch 1) negBefore (po :: curExcluded) resSub.2 h_all' h_neg h_sub h_excl' h_ok with h_red | h_bound
            · exact Or.inl h_red
            · right
              simp only [activeOutletSum, h_act, Bool.false_eq_true, ↓reduceIte]
              omega

/-- `MatchesCartState31` lifting of `checkBoundRec_sound`:
    whenever `(checkBoundRec deg fuel st forcedIn negBefore rem excluded maxch hs).1 = true`
    on `st` satisfying `MatchesCartState31 deg cartDeg st`, either `HasExactReducedAxle deg cartDeg`
    holds directly (via `reduceAxleRec_sound`), or the active outlet sum plus `forcedIn` is at most `maxch`. -/
theorem checkBoundRec_sound31 (deg : Nat) (cartDeg : Nat → Nat) (h_deg : deg ≤ 11) (fuel : Nat) :
    ∀ (st forcedIn : Nat) (negBefore rem excluded : List FastPosOut) (maxch : Nat) (hs : HintStream),
      MatchesCartState31 deg cartDeg st →
      (∀ po ∈ negBefore, validFastPosOut deg po = true ∧ po.isPos = false) →
      (∀ po ∈ rem, validFastPosOut deg po = true) →
      (∀ ex ∈ excluded, OutletActive deg cartDeg ex = false) →
      (checkBoundRec deg fuel st forcedIn negBefore rem excluded maxch hs).1 = true →
      HasExactReducedAxle deg cartDeg ∨
      (forcedIn : Int) + activeOutletSum deg cartDeg negBefore + activeOutletSum deg cartDeg rem ≤ (maxch : Int) := by
  induction fuel with
  | zero =>
    intro st forcedIn negBefore rem excluded maxch hs _ _ _ _ h_ok
    rw [checkBoundRec_zero] at h_ok
    contradiction
  | succ fuel ih =>
    intro st forcedIn negBefore rem excluded maxch hs h_match31 h_neg h_rem h_excl h_ok
    rw [checkBoundRec_succ_eq] at h_ok
    have h_fneg := filterNegAPS_sound deg cartDeg st h_deg h_match31.1 negBefore forcedIn h_neg
    let forced1 := (filterNegAPS st negBefore forcedIn).1
    let nextNegBefore := (filterNegAPS st negBefore forcedIn).2
    have h_frem := filterRemAPS_sound deg cartDeg st h_deg h_match31.1 rem forced1 h_rem
    let forcedch := (filterRemAPS st rem forced1).1
    let allowedch := (filterRemAPS st rem forced1).2.1
    let nextRem := (filterRemAPS st rem forced1).2.2
    change (@Bool.rec (fun _ => Bool × HintStream)
      (@Bool.rec (fun _ => Bool × HintStream)
        (checkBoundLoopRec (checkBoundRec deg fuel) st forcedch maxch nextRem allowedch nextNegBefore excluded hs)
        (reduceAxleRec deg 64 [st] hs)
        (Nat.ble (Nat.add maxch 1) forcedch))
      (true, hs)
      (Nat.ble (Nat.add forcedch allowedch) maxch)).1 = true at h_ok
    cases h_ble1 : Nat.ble (Nat.add forcedch allowedch) maxch with
    | true =>
      right
      have h_le : forcedch + allowedch ≤ maxch := Nat.le_of_ble_eq_true h_ble1
      have h_neg_le : activeOutletSum deg cartDeg nextNegBefore ≤ 0 :=
        activeOutletSum_le_zero_of_all_neg deg cartDeg nextNegBefore (fun q hq => (h_fneg.1 q hq).2)
      have h_rem_le : activeOutletSum deg cartDeg nextRem ≤ (countPos nextRem : Int) :=
        activeOutletSum_le_countPos deg cartDeg nextRem
      have h_all_eq : allowedch = countPos nextRem := h_frem.2.1
      have h1 : (forcedIn : Int) + activeOutletSum deg cartDeg negBefore ≤
          (forced1 : Int) + activeOutletSum deg cartDeg nextNegBefore := h_fneg.2
      have h2 : (forced1 : Int) + activeOutletSum deg cartDeg rem ≤
          (forcedch : Int) + activeOutletSum deg cartDeg nextRem := h_frem.2.2
      omega
    | false =>
      rw [h_ble1] at h_ok; dsimp only at h_ok
      cases h_ble2 : Nat.ble (Nat.add maxch 1) forcedch with
      | true =>
        rw [h_ble2] at h_ok; dsimp only at h_ok
        exact Or.inl (reduceAxleRec_sound deg cartDeg h_deg 64 [st] hs ⟨st, List.mem_cons_self, h_match31⟩ h_ok)
      | false =>
        rw [h_ble2] at h_ok; dsimp only at h_ok
        rcases checkBoundLoopRec_sound31 deg cartDeg h_deg (checkBoundRec deg fuel) ih
          st forcedch maxch h_match31 nextRem allowedch nextNegBefore excluded hs
          h_frem.2.1 h_fneg.1 h_frem.1 h_excl h_ok with h_red | h_bound
        · exact Or.inl h_red
        · right
          have h1 : (forcedIn : Int) + activeOutletSum deg cartDeg negBefore ≤
              (forced1 : Int) + activeOutletSum deg cartDeg nextNegBefore := h_fneg.2
          have h2 : (forced1 : Int) + activeOutletSum deg cartDeg rem ≤
              (forcedch : Int) + activeOutletSum deg cartDeg nextRem := h_frem.2.2
          omega

/-- `MatchesCartState31` lifting of `verifyHubcapMembersRec_sound`:
    whenever `(verifyHubcapMembersRec deg st shiftedTable members hs).1 = true` on `st`
    satisfying `MatchesCartState31 deg cartDeg st`, either `HasExactReducedAxle deg cartDeg` holds,
    or EVERY hubcap member `(x, y, v) ∈ members` satisfies the LP bound. -/
theorem verifyHubcapMembersRec_sound31 (deg : Nat) (cartDeg : Nat → Nat) (h_deg : deg ≤ 11)
    (st : Nat) (h_match31 : MatchesCartState31 deg cartDeg st)
    (shiftedTable : List (List FastPosOut))
    (h_table : ∀ row ∈ shiftedTable, ∀ po ∈ row, validFastPosOut deg po = true)
    (members : List (Nat × Nat × Int)) :
    ∀ (hs : HintStream),
      (verifyHubcapMembersRec deg st shiftedTable members hs).1 = true →
      HasExactReducedAxle deg cartDeg ∨
      ∀ m ∈ members,
        500 + activeOutletSum deg cartDeg
          (if Nat.beq m.1 m.2.1 then lookupListRec [] shiftedTable m.1
           else lookupListRec [] shiftedTable m.1 ++ lookupListRec [] shiftedTable m.2.1) ≤
          ((m.2.2 + 500).toNat : Int) := by
  induction members with
  | nil =>
    intro _ _
    exact Or.inr (fun _ hm => by contradiction)
  | cons m rest ih =>
    intro hs h_ok
    rw [verifyHubcapMembersRec_cons] at h_ok
    rcases m with ⟨x, y, v⟩
    dsimp only at h_ok
    simp only [strictNat_eq] at h_ok
    let outsX := lookupListRec [] shiftedTable x
    let outsY := lookupListRec [] shiftedTable y
    let initRem :=
      @Bool.rec (fun _ => List FastPosOut)
        outsX
        (appendFastPosOut outsX outsY)
        (!Nat.beq x y)
    let resCB := checkBoundRec deg 20 st 500 [] initRem [] (v + 500).toNat hs
    change (@Bool.rec (fun _ => Bool × HintStream) (false, resCB.2)
      (verifyHubcapMembersRec deg st shiftedTable rest resCB.2) resCB.1).1 = true at h_ok
    cases h_cb : resCB.1 with
    | false =>
      rw [h_cb] at h_ok; dsimp only at h_ok; contradiction
    | true =>
      rw [h_cb] at h_ok; dsimp only at h_ok
      have h_init_valid : ∀ po ∈ initRem, validFastPosOut deg po = true := by
        dsimp [initRem]
        cases (!Nat.beq x y) with
        | false =>
          exact validFastPosOut_lookupListRec deg shiftedTable h_table x
        | true =>
          dsimp only
          rw [appendFastPosOut_eq_append]
          intro po hpo
          rcases List.mem_append.mp hpo with hX | hY
          · exact validFastPosOut_lookupListRec deg shiftedTable h_table x po hX
          · exact validFastPosOut_lookupListRec deg shiftedTable h_table y po hY
      rcases checkBoundRec_sound31 deg cartDeg h_deg 20 st 500 [] initRem [] (v + 500).toNat hs
        h_match31 (by intro _ h; contradiction) h_init_valid (by intro _ h; contradiction) h_cb with h_red | h_bound
      · exact Or.inl h_red
      · rcases ih resCB.2 h_ok with h_red | h_rest
        · exact Or.inl h_red
        · right
          intro m' hm'
          rcases List.mem_cons.mp hm' with rfl | hm_rest
          · dsimp only
            have h_init_eq : initRem = (if Nat.beq x y then outsX else outsX ++ outsY) := by
              dsimp [initRem]
              cases Nat.beq x y with
              | true => rfl
              | false => exact appendFastPosOut_eq_append outsX outsY
            rw [← h_init_eq]
            simpa [activeOutletSum] using h_bound
          · exact h_rest m' hm_rest

/-!
### Stage M.2: Computable RSST Hubcap Cover Validity & Hub Charge Arithmetic Bridge
-/

/-- Number of hubcap members `(x, y, v) ∈ members` incident to spoke `i` (`x == i || y == i`). -/
def hubcapSpokeOcc : List (Nat × Nat × Int) → Nat → Nat
  | [], _ => 0
  | m :: rest, i => (if Nat.beq m.1 i || Nat.beq m.2.1 i then 1 else 0) + hubcapSpokeOcc rest i

/-- RSST weight `w(m) ∈ {1, 2}` of a hubcap member `m = (x, y, v)` in `members`. -/
def hubcapMemberWeight (members : List (Nat × Nat × Int)) (m : Nat × Nat × Int) : Nat :=
  if Nat.beq (hubcapSpokeOcc members m.1) 1 then 2 else 1

/-- Total weight of members in `l` incident to spoke `i` using weight function `w`. -/
def hubcapSpokeWeightSum (w : Nat × Nat × Int → Nat) (i : Nat) : List (Nat × Nat × Int) → Nat
  | [] => 0
  | m :: rest =>
    (if Nat.beq m.1 i || Nat.beq m.2.1 i then w m else 0) + hubcapSpokeWeightSum w i rest

/-- Weighted sum of upper bounds `w(m) * v` over `m = (x, y, v) ∈ l`. -/
def hubcapWeightedBoundSum (w : Nat × Nat × Int → Nat) : List (Nat × Nat × Int) → Int
  | [] => 0
  | m :: rest => (w m : Int) * m.2.2 + hubcapWeightedBoundSum w rest

/-- Computable RSST Hubcap Cover Validity Predicate for hub degree `deg`:
    1. Every member `(x, y, v) ∈ members` has `1 ≤ x, y ≤ deg` and `-500 ≤ v`.
    2. Every spoke `i ∈ [1..deg]` is covered with total weight `2`.
    3. The weighted sum of bounds is at most `20 * (deg - 6) + 1`. -/
def validHubcapCover (deg : Nat) (members : List (Nat × Nat × Int)) : Bool :=
  let w := hubcapMemberWeight members
  members.all (fun m =>
    Nat.ble 1 m.1 && Nat.ble m.1 deg &&
    Nat.ble 1 m.2.1 && Nat.ble m.2.1 deg &&
    decide (-500 ≤ m.2.2)) &&
  (List.range' 1 deg).all (fun i =>
    Nat.beq (hubcapSpokeWeightSum w i members) 2) &&
  decide (hubcapWeightedBoundSum w members ≤ 20 * ((deg : Int) - 6) + 1)

/-- Explicit non-vacuity lemma: the empty hubcap `[]` is never a valid cover for any `deg ≥ 1`. -/
theorem not_validHubcapCover_nil (deg : Nat) (h_deg : 1 ≤ deg) :
    validHubcapCover deg [] = false := by
  rcases Nat.exists_eq_add_of_le h_deg with ⟨k, rfl⟩
  have h_r : List.range' 1 (1 + k) = 1 :: List.range' 2 k := by
    rw [Nat.add_comm 1 k]
    rfl
  simp [validHubcapCover, h_r, hubcapSpokeWeightSum]

/-- Sum of an integer-valued function `f : Nat → Int` over a list of indices `idxs : List Nat`. -/
def sumNatList (f : Nat → Int) : List Nat → Int
  | [] => 0
  | i :: rest => f i + sumNatList f rest

theorem foldl_add_eq_add_sumNatList (f : Nat → Int) (l : List Nat) (init : Int) :
    l.foldl (fun acc i => acc + f i) init = init + sumNatList f l := by
  induction l generalizing init with
  | nil => simp [sumNatList]
  | cons i rest ih =>
    simp only [List.foldl_cons, sumNatList]
    rw [ih (init + f i)]
    omega

theorem sumNatList_add (f g : Nat → Int) (l : List Nat) :
    sumNatList (fun i => f i + g i) l = sumNatList f l + sumNatList g l := by
  induction l with
  | nil => simp [sumNatList]
  | cons i rest ih =>
    simp only [sumNatList, ih]
    omega

theorem sumNatList_const_mul (c : Int) (f : Nat → Int) (l : List Nat) :
    sumNatList (fun i => c * f i) l = c * sumNatList f l := by
  induction l with
  | nil => simp [sumNatList]
  | cons i rest ih =>
    simp only [sumNatList, ih, Int.mul_add]

theorem sumNatList_congr {f g : Nat → Int} {l : List Nat} (h : ∀ i ∈ l, f i = g i) :
    sumNatList f l = sumNatList g l := by
  induction l with
  | nil => rfl
  | cons i rest ih =>
    simp only [sumNatList]
    rw [h i List.mem_cons_self, ih (fun j hj => h j (List.mem_cons_of_mem i hj))]

theorem sumNatList_ite_beq_range' (f : Nat → Int) (x : Nat) :
    ∀ (s n : Nat),
      sumNatList (fun i => if Nat.beq x i then f i else 0) (List.range' s n) =
        if s ≤ x ∧ x < s + n then f x else 0 := by
  intro s n
  induction n generalizing s with
  | zero =>
    simp only [List.range', sumNatList]
    split
    · omega
    · rfl
  | succ n ih =>
    simp only [List.range'_succ, sumNatList, ih (s + 1)]
    cases h_beq : Nat.beq x s with
    | true =>
      have hxs : x = s := Nat.beq_eq.mp h_beq
      subst hxs
      simp only [↓reduceIte]
      have h_not : ¬(x + 1 ≤ x ∧ x < x + 1 + n) := by omega
      have h_yes : x ≤ x ∧ x < x + (n + 1) := by omega
      rw [if_neg h_not, if_pos h_yes]
      omega
    | false =>
      have hxs : x ≠ s := fun h => by subst h; rw [Nat.beq_refl] at h_beq; contradiction
      simp only [Bool.false_eq_true, ↓reduceIte, Int.zero_add]
      by_cases h_in : s + 1 ≤ x ∧ x < s + 1 + n
      · have h_in' : s ≤ x ∧ x < s + (n + 1) := by omega
        rw [if_pos h_in, if_pos h_in']
      · have h_in' : ¬(s ≤ x ∧ x < s + (n + 1)) := by omega
        rw [if_neg h_in, if_neg h_in']

theorem activeOutletSum_member_eq_sumNatList (deg : Nat) (cartDeg : Nat → Nat)
    (shiftedTable : List (List FastPosOut)) {x y : Nat}
    (hx1 : 1 ≤ x) (hx2 : x ≤ deg) (hy1 : 1 ≤ y) (hy2 : y ≤ deg) :
    activeOutletSum deg cartDeg
      (if Nat.beq x y then lookupListRec [] shiftedTable x
       else lookupListRec [] shiftedTable x ++ lookupListRec [] shiftedTable y) =
    sumNatList
      (fun i => if Nat.beq x i || Nat.beq y i then
        activeOutletSum deg cartDeg (lookupListRec [] shiftedTable i) else 0)
      (List.range' 1 deg) := by
  let S := fun i => activeOutletSum deg cartDeg (lookupListRec [] shiftedTable i)
  cases hxy : Nat.beq x y with
  | true =>
    have h_eq : x = y := Nat.beq_eq.mp hxy
    subst h_eq
    simp only [Bool.or_self, ↓reduceIte]
    rw [sumNatList_ite_beq_range' S x 1 deg, if_pos ⟨hx1, by omega⟩]
  | false =>
    have h_ne : x ≠ y := fun h => by subst h; rw [Nat.beq_refl] at hxy; contradiction
    simp only [Bool.false_eq_true, ↓reduceIte, activeOutletSum_append]
    have h_split :
        sumNatList (fun i => if Nat.beq x i || Nat.beq y i then S i else 0) (List.range' 1 deg) =
        sumNatList (fun i => (if Nat.beq x i then S i else 0) + (if Nat.beq y i then S i else 0)) (List.range' 1 deg) := by
      apply sumNatList_congr
      intro i _
      cases hxi : Nat.beq x i with
      | false => simp
      | true =>
        have h_xi : x = i := Nat.beq_eq.mp hxi
        have hyi : Nat.beq y i = false := by
          cases h_yi : Nat.beq y i with
          | false => rfl
          | true =>
            have h_yi_eq : y = i := Nat.beq_eq.mp h_yi
            omega
        simp [hyi]
    rw [h_split, sumNatList_add, sumNatList_ite_beq_range' S x 1 deg, sumNatList_ite_beq_range' S y 1 deg,
        if_pos ⟨hx1, by omega⟩, if_pos ⟨hy1, by omega⟩]

theorem sumNatList_hubcapSpokeWeightSum_le_weightedBoundSum
    (deg : Nat) (cartDeg : Nat → Nat) (shiftedTable : List (List FastPosOut))
    (w : Nat × Nat × Int → Nat) (l : List (Nat × Nat × Int))
    (h_valid : ∀ m ∈ l, 1 ≤ m.1 ∧ m.1 ≤ deg ∧ 1 ≤ m.2.1 ∧ m.2.1 ≤ deg ∧ -500 ≤ m.2.2)
    (h_bounds : ∀ m ∈ l,
      500 + activeOutletSum deg cartDeg
        (if Nat.beq m.1 m.2.1 then lookupListRec [] shiftedTable m.1
         else lookupListRec [] shiftedTable m.1 ++ lookupListRec [] shiftedTable m.2.1) ≤
        ((m.2.2 + 500).toNat : Int)) :
    sumNatList
      (fun i => (hubcapSpokeWeightSum w i l : Int) *
        activeOutletSum deg cartDeg (lookupListRec [] shiftedTable i))
      (List.range' 1 deg) ≤
    hubcapWeightedBoundSum w l := by
  let S := fun i => activeOutletSum deg cartDeg (lookupListRec [] shiftedTable i)
  induction l with
  | nil =>
    have h_zero :
        sumNatList (fun i => (hubcapSpokeWeightSum w i [] : Int) * S i) (List.range' 1 deg) =
        sumNatList (fun _ => 0) (List.range' 1 deg) := by
      apply sumNatList_congr
      intro i _
      simp [hubcapSpokeWeightSum]
    rw [h_zero]
    have h_z2 : ∀ l' : List Nat, sumNatList (fun _ => 0) l' = 0 := by
      intro l'; induction l' with
      | nil => rfl
      | cons _ _ ih => simp [sumNatList, ih]
    rw [h_z2]
    exact Int.le_refl 0
  | cons m rest ih =>
    have hm_val := h_valid m List.mem_cons_self
    rcases hm_val with ⟨hx1, hx2, hy1, hy2, hv500⟩
    have hm_b := h_bounds m List.mem_cons_self
    have hm_le :
        activeOutletSum deg cartDeg
          (if Nat.beq m.1 m.2.1 then lookupListRec [] shiftedTable m.1
           else lookupListRec [] shiftedTable m.1 ++ lookupListRec [] shiftedTable m.2.1) ≤ m.2.2 := by
      omega
    rw [activeOutletSum_member_eq_sumNatList deg cartDeg shiftedTable hx1 hx2 hy1 hy2] at hm_le
    have h_w_le := Int.mul_le_mul_of_nonneg_left hm_le (Int.natCast_nonneg (w m))
    rw [← sumNatList_const_mul] at h_w_le
    have h_ih := ih
      (fun m' hm' => h_valid m' (List.mem_cons_of_mem m hm'))
      (fun m' hm' => h_bounds m' (List.mem_cons_of_mem m hm'))
    have h_step :
        sumNatList (fun i => (hubcapSpokeWeightSum w i (m :: rest) : Int) * S i) (List.range' 1 deg) =
        sumNatList (fun i => (w m : Int) * (if Nat.beq m.1 i || Nat.beq m.2.1 i then S i else 0)) (List.range' 1 deg) +
        sumNatList (fun i => (hubcapSpokeWeightSum w i rest : Int) * S i) (List.range' 1 deg) := by
      rw [← sumNatList_add]
      apply sumNatList_congr
      intro i _
      dsimp only [hubcapSpokeWeightSum]
      cases Nat.beq m.1 i || Nat.beq m.2.1 i <;> simp [Int.natCast_add, Int.add_mul]
    rw [h_step]
    dsimp [hubcapWeightedBoundSum]
    dsimp [S] at h_w_le h_ih ⊢
    omega

/-- Fundamental RSST Hubcap Arithmetic Soundness Theorem:
    whenever `validHubcapCover deg members = true` and every member `m ∈ members` satisfies
    the verified `checkBoundRec` inequality, the hub's initial charge `10 * (6 - deg)` plus
    the total active outlet sum across all spokes `1 .. deg` is at most `0`. -/
theorem activeOutletSum_hub_le_of_validHubcapCover
    (deg : Nat) (cartDeg : Nat → Nat) (shiftedTable : List (List FastPosOut))
    (members : List (Nat × Nat × Int))
    (h_cover : validHubcapCover deg members = true)
    (h_bounds : ∀ m ∈ members,
      500 + activeOutletSum deg cartDeg
        (if Nat.beq m.1 m.2.1 then lookupListRec [] shiftedTable m.1
         else lookupListRec [] shiftedTable m.1 ++ lookupListRec [] shiftedTable m.2.1) ≤
        ((m.2.2 + 500).toNat : Int)) :
    10 * (6 - (deg : Int)) +
      (List.range' 1 deg).foldl
        (fun acc i => acc + activeOutletSum deg cartDeg (lookupListRec [] shiftedTable i)) 0 ≤ 0 := by
  rw [foldl_add_eq_add_sumNatList, Int.zero_add]
  let w := hubcapMemberWeight members
  let S := fun i => activeOutletSum deg cartDeg (lookupListRec [] shiftedTable i)
  dsimp [validHubcapCover] at h_cover
  rcases Bool.and_eq_true_iff.mp h_cover with ⟨h_cov12, h_sum_le_b⟩
  rcases Bool.and_eq_true_iff.mp h_cov12 with ⟨h_all_mem, h_all_spokes⟩
  have h_sum_le : hubcapWeightedBoundSum w members ≤ 20 * ((deg : Int) - 6) + 1 :=
    of_decide_eq_true h_sum_le_b
  have h_valid : ∀ m ∈ members, 1 ≤ m.1 ∧ m.1 ≤ deg ∧ 1 ≤ m.2.1 ∧ m.2.1 ≤ deg ∧ -500 ≤ m.2.2 := by
    intro m hm
    have hm_b := List.all_eq_true.mp h_all_mem m hm
    rcases Bool.and_eq_true_iff.mp hm_b with ⟨hb1234, hb5⟩
    rcases Bool.and_eq_true_iff.mp hb1234 with ⟨hb123, hb4⟩
    rcases Bool.and_eq_true_iff.mp hb123 with ⟨hb12, hb3⟩
    rcases Bool.and_eq_true_iff.mp hb12 with ⟨hb1, hb2⟩
    exact ⟨Nat.le_of_ble_eq_true hb1, Nat.le_of_ble_eq_true hb2,
           Nat.le_of_ble_eq_true hb3, Nat.le_of_ble_eq_true hb4,
           of_decide_eq_true hb5⟩
  have h_le_wb := sumNatList_hubcapSpokeWeightSum_le_weightedBoundSum deg cartDeg shiftedTable w members h_valid h_bounds
  have h_eq_two :
      sumNatList (fun i => (hubcapSpokeWeightSum w i members : Int) * S i) (List.range' 1 deg) =
      2 * sumNatList S (List.range' 1 deg) := by
    rw [← sumNatList_const_mul]
    apply sumNatList_congr
    intro i hi
    have hi_eq : hubcapSpokeWeightSum w i members = 2 :=
      Nat.beq_eq.mp (List.all_eq_true.mp h_all_spokes i hi)
    rw [hi_eq]
    rfl
  dsimp [S] at h_eq_two
  omega

/-- Computable structural validity check on `t : ProofTree` at hub degree `deg` with remaining depth budget `maxLev`:
    - Every `ProofTree.cond v m tTrue tFalse` has `maxLev ≥ 1` and `1 ≤ v ≤ 5 * deg`.
    - Every `ProofTree.hubcap members` satisfies `validHubcapCover deg members = true`. -/
def validProofTree (deg : Nat) : Nat → ProofTree → Bool
  | _, ProofTree.reduce => true
  | _, ProofTree.sym _ _ _ _ => true
  | _, ProofTree.hubcap members => validHubcapCover deg members
  | 0, ProofTree.cond _ _ _ _ => false
  | maxLev + 1, ProofTree.cond v _ tTrue tFalse =>
    Nat.ble 1 v && Nat.ble v (Nat.mul 5 deg) &&
    validProofTree deg maxLev tTrue &&
    validProofTree deg maxLev tFalse

set_option maxRecDepth 2000000 in
theorem validProofTree_present7 : validProofTree 7 58 (present7 ()) = true := by decide

set_option maxRecDepth 2000000 in
theorem validProofTree_present8 : validProofTree 8 58 (present8 ()) = true := by decide

set_option maxRecDepth 2000000 in
theorem validProofTree_present9 : validProofTree 9 58 (present9 ()) = true := by decide

set_option maxRecDepth 2000000 in
theorem validProofTree_present10 : validProofTree 10 58 (present10 ()) = true := by decide

set_option maxRecDepth 2000000 in
theorem validProofTree_present11 : validProofTree 11 58 (present11 ()) = true := by decide

/-!
### Stage M.3: Non-Vacuous 2-Way `CoreCartLeaf` & Elimination of `ProofTree.sym`
-/

/-- Non-vacuous 2-way core leaf certificate for a cartwheel degree assignment `cartDeg`:
    either (1) `cartDeg` has an exact reduced axle configuration (`HasExactReducedAxle`),
    or (2) `cartDeg` satisfies all LP bounds of a structurally valid RSST hubcap cover
       (`validHubcapCover deg members = true`). -/
def CoreCartLeaf (deg : Nat) (shiftedTable : List (List FastPosOut)) (cartDeg : Nat → Nat) : Prop :=
  HasExactReducedAxle deg cartDeg ∨
  (∃ members : List (Nat × Nat × Int),
    validHubcapCover deg members = true ∧
    ∀ m ∈ members,
      500 + activeOutletSum deg cartDeg
        (if Nat.beq m.1 m.2.1 then lookupListRec [] shiftedTable m.1
         else lookupListRec [] shiftedTable m.1 ++ lookupListRec [] shiftedTable m.2.1) ≤
        ((m.2.2 + 500).toNat : Int))

/-- Every `CoreCartLeaf` either has an exact reduced axle configuration (`HasExactReducedAxle`)
    or satisfies the non-positive hub charge inequality
    `10 * (6 - deg) + ∑_{i=1..deg} activeOutletSum(i) ≤ 0`. -/
theorem coreCartLeaf_reducible_or_hub_sum_le_zero
    (deg : Nat) (shiftedTable : List (List FastPosOut)) (cartDeg : Nat → Nat)
    (h_core : CoreCartLeaf deg shiftedTable cartDeg) :
    HasExactReducedAxle deg cartDeg ∨
    10 * (6 - (deg : Int)) +
      (List.range' 1 deg).foldl
        (fun acc i => acc + activeOutletSum deg cartDeg (lookupListRec [] shiftedTable i)) 0 ≤ 0 := by
  rcases h_core with h_red | ⟨members, h_cover, h_bounds⟩
  · exact Or.inl h_red
  · exact Or.inr (activeOutletSum_hub_le_of_validHubcapCover deg cartDeg shiftedTable members h_cover h_bounds)

/-- A cartwheel degree assignment `cd` satisfies the condition prefix stored in lanes `0 .. lev - 1`
    of `(condV, condM)` if for every `i < lev`, the bitmask in lane `i` of `condM` has the bit
    for `cd (getLaneNat condV i)` set. -/
def SatisfiesPrefix (cd : Nat → Nat) (condV condM lev : Nat) : Prop :=
  ∀ i < lev, (getLaneNat condM i).testBit (degBitIdx (cd (getLaneNat condV i))) = true

theorem extractCondsRec_eq_none_of_getLaneNat_zero (deg condV condM lev : Nat)
    (h_zero : getLaneNat condV lev = 0) :
    extractCondsRec deg condV condM lev = none := by
  rw [extractCondsRec_eq_loop]
  cases lev with
  | zero =>
    change (strictNat (getLaneNat condV 0) fun n =>
      @Bool.rec (fun _ => Option (List (Nat × Nat))) none
        (some ((n, getLaneNat condM 0) :: []))
        (Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg))) = none
    rw [strictNat_eq, h_zero]
    rfl
  | succ i =>
    change (strictNat (Nat.add i 1) fun idx =>
      strictNat (getLaneNat condV idx) fun n =>
      @Bool.rec (fun _ => Option (List (Nat × Nat))) none
        (extractCondsLoop deg condV condM i ((n, getLaneNat condM idx) :: []))
        (Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg))) = none
    rw [strictNat_eq, strictNat_eq]
    have h_idx : Nat.add i 1 = i + 1 := rfl
    rw [h_idx, h_zero]
    rfl

theorem extractCondsLoop_sublist (deg condV condM : Nat) :
    ∀ (k : Nat) (acc res : List (Nat × Nat)),
      extractCondsLoop deg condV condM k acc = some res →
      (∀ c ∈ acc, c ∈ res) ∧
      (∀ j ≤ k, (getLaneNat condV j, getLaneNat condM j) ∈ res) := by
  intro k
  induction k with
  | zero =>
    intro acc res h_some
    change (strictNat (getLaneNat condV 0) fun n =>
      @Bool.rec (fun _ => Option (List (Nat × Nat))) none
        (some ((n, getLaneNat condM 0) :: acc))
        (Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg))) = some res at h_some
    rw [strictNat_eq] at h_some
    let n := getLaneNat condV 0
    cases h_b : (Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg)) with
    | false => rw [h_b] at h_some; contradiction
    | true =>
      rw [h_b] at h_some
      dsimp only at h_some
      injection h_some with h_eq
      subst h_eq
      refine ⟨fun c hc => List.mem_cons_of_mem _ hc, ?_⟩
      intro j hj
      have hj0 : j = 0 := by omega
      subst hj0
      exact List.mem_cons_self
  | succ i ih =>
    intro acc res h_some
    unfold extractCondsLoop at h_some
    dsimp only at h_some
    rw [strictNat_eq, strictNat_eq] at h_some
    let idx := Nat.add i 1
    let n := getLaneNat condV idx
    change (@Bool.rec (fun _ => Option (List (Nat × Nat))) none
      (extractCondsLoop deg condV condM i ((n, getLaneNat condM idx) :: acc))
      (Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg))) = some res at h_some
    cases h_b : (Nat.ble 1 n && Nat.ble n (Nat.mul 2 deg)) with
    | false => rw [h_b] at h_some; contradiction
    | true =>
      rw [h_b] at h_some
      dsimp only at h_some
      have ⟨h_acc, h_le⟩ := ih ((n, getLaneNat condM idx) :: acc) res h_some
      refine ⟨fun c hc => h_acc c (List.mem_cons_of_mem _ hc), ?_⟩
      intro j hj
      by_cases hji : j ≤ i
      · exact h_le j hji
      · have hj_eq : j = idx := by change j = i + 1; omega
        subst hj_eq
        exact h_acc _ List.mem_cons_self

theorem satisfiesPrefix_of_extractCondsRec (deg condV condM lev : Nat)
    {conds : List (Nat × Nat)} (h_some : extractCondsRec deg condV condM lev = some conds)
    (cd : Nat → Nat)
    (h_sat : ∀ c ∈ conds, c.2.testBit (degBitIdx (cd c.1)) = true) :
    SatisfiesPrefix cd condV condM (lev + 1) := by
  rw [extractCondsRec_eq_loop] at h_some
  have ⟨_, h_mem⟩ := extractCondsLoop_sublist deg condV condM lev [] conds h_some
  intro j hj
  exact h_sat (getLaneNat condV j, getLaneNat condM j) (h_mem j (by omega))

theorem satisfiesPrefix_cond_iff (cd : Nat → Nat) (condV condM lev v maskTrue : Nat)
    (h_lev : lev + 1 < 60) :
    SatisfiesPrefix cd
      (setLaneNat (setLaneNat condV lev v) (Nat.add lev 1) 0)
      (setLaneNat (setLaneNat condM lev maskTrue) (Nat.add lev 1) 0)
      lev ↔
    SatisfiesPrefix cd condV condM lev := by
  constructor <;> intro h i hi
  · have hi60 : i < 60 := by omega
    have hi_ne1 : i ≠ Nat.add lev 1 := by change i ≠ lev + 1; omega
    have hi_ne0 : i ≠ lev := by omega
    have h_i := h i hi
    rw [getLaneNat_setLaneNat_ne _ (Nat.add lev 1) 0 i hi60 hi_ne1,
        getLaneNat_setLaneNat_ne _ lev maskTrue i hi60 hi_ne0,
        getLaneNat_setLaneNat_ne _ (Nat.add lev 1) 0 i hi60 hi_ne1,
        getLaneNat_setLaneNat_ne _ lev v i hi60 hi_ne0] at h_i
    exact h_i
  · have hi60 : i < 60 := by omega
    have hi_ne1 : i ≠ Nat.add lev 1 := by change i ≠ lev + 1; omega
    have hi_ne0 : i ≠ lev := by omega
    rw [getLaneNat_setLaneNat_ne _ (Nat.add lev 1) 0 i hi60 hi_ne1,
        getLaneNat_setLaneNat_ne _ lev maskTrue i hi60 hi_ne0,
        getLaneNat_setLaneNat_ne _ (Nat.add lev 1) 0 i hi60 hi_ne1,
        getLaneNat_setLaneNat_ne _ lev v i hi60 hi_ne0]
    exact h i hi

theorem satisfiesPrefix_cond_succ_iff (cd : Nat → Nat) (condV condM lev v maskTrue : Nat)
    (h_lev : lev + 1 < 60) (hv64 : v < 64) :
    SatisfiesPrefix cd
      (setLaneNat (setLaneNat condV lev v) (Nat.add lev 1) 0)
      (setLaneNat (setLaneNat condM lev maskTrue) (Nat.add lev 1) 0)
      (Nat.add lev 1) ↔
    (SatisfiesPrefix cd condV condM lev ∧
     maskTrue.testBit (degBitIdx (cd v)) = true) := by
  let condV' := setLaneNat (setLaneNat condV lev v) (Nat.add lev 1) 0
  let condM' := setLaneNat (setLaneNat condM lev maskTrue) (Nat.add lev 1) 0
  have h_lev60 : lev < 60 := by omega
  have h_ne1 : lev ≠ Nat.add lev 1 := by change lev ≠ lev + 1; omega
  have h_v_eq : getLaneNat condV' lev = v := by
    dsimp [condV']
    rw [getLaneNat_setLaneNat_ne _ (Nat.add lev 1) 0 lev h_lev60 h_ne1,
        getLaneNat_setLaneNat_self condV lev v h_lev60 hv64]
  have h_m_tb : (getLaneNat condM' lev).testBit (degBitIdx (cd v)) = maskTrue.testBit (degBitIdx (cd v)) := by
    dsimp [condM']
    rw [getLaneNat_setLaneNat_ne _ (Nat.add lev 1) 0 lev h_lev60 h_ne1,
        testBit_getLaneNat_setLaneNat_self condM lev maskTrue h_lev60 (degBitIdx_lt_6 _)]
  constructor
  · intro h
    refine ⟨(satisfiesPrefix_cond_iff cd condV condM lev v maskTrue h_lev).mp (fun i hi => h i (by change i < lev + 1; omega)), ?_⟩
    have h_at := h lev (by change lev < lev + 1; omega)
    rw [h_v_eq, h_m_tb] at h_at
    exact h_at
  · rintro ⟨h_pre, h_tb⟩ i hi
    have hi_le : i ≤ lev := by change i < lev + 1 at hi; omega
    by_cases hi_lt : i < lev
    · exact (satisfiesPrefix_cond_iff cd condV condM lev v maskTrue h_lev).mpr h_pre i hi_lt
    · have hi_eq : i = lev := by omega
      subst hi_eq
      rw [h_v_eq, h_m_tb]
      exact h_tb

theorem matchesCartState31_cond_true (deg : Nat) (cartDeg : Nat → Nat) (st v : Nat) (m : Int)
    (h_deg : deg ≤ 11) (h_match31 : MatchesCartState31 deg cartDeg st)
    (h_true : (condMaskNat m).testBit (degBitIdx (cartDeg v)) = true) :
    MatchesCartState31 deg cartDeg (setLaneNat st v (Nat.land (getLaneNat st v) (condMaskNat m))) := by
  refine ⟨?_, ?_⟩
  · intro p hp1 hp2
    have hp60 : p < 60 := by omega
    by_cases hpv : p = v
    · subst hpv
      rw [testBit_getLaneNat_setLaneNat_self _ _ _ hp60 (degBitIdx_lt_6 _)]
      change ((getLaneNat st p) &&& (condMaskNat m)).testBit (degBitIdx (cartDeg p)) = true
      rw [Nat.testBit_and, h_match31.1 p hp1 hp2, h_true]
      rfl
    · rw [testBit_getLaneNat_setLaneNat_ne _ _ _ p hp60 hpv (degBitIdx_lt_6 _)]
      exact h_match31.1 p hp1 hp2
  · intro p hp1 hp2
    have hp60 : p < 60 := by omega
    change getLaneNat (setLaneNat st v (getLaneNat st v &&& condMaskNat m)) p ≤ 31
    by_cases hpv : p = v
    · subst hpv
      have h_le : getLaneNat st p &&& condMaskNat m ≤ 31 :=
        Nat.le_trans Nat.and_le_left (h_match31.2 p hp1 hp2)
      rw [getLaneNat_setLaneNat_self st p (getLaneNat st p &&& condMaskNat m) hp60 (by omega)]
      exact h_le
    · rw [getLaneNat_setLaneNat_ne st v (getLaneNat st v &&& condMaskNat m) p hp60 hpv]
      exact h_match31.2 p hp1 hp2

theorem matchesCartState31_cond_false (deg : Nat) (cartDeg : Nat → Nat) (st v : Nat) (m : Int)
    (h_deg : deg ≤ 11) (h_match31 : MatchesCartState31 deg cartDeg st)
    (h_false : (condMaskNat m).testBit (degBitIdx (cartDeg v)) = false) :
    MatchesCartState31 deg cartDeg (setLaneNat st v (Nat.land (getLaneNat st v) (Nat.xor 31 (condMaskNat m)))) := by
  refine ⟨?_, ?_⟩
  · intro p hp1 hp2
    have hp60 : p < 60 := by omega
    by_cases hpv : p = v
    · subst hpv
      rw [testBit_getLaneNat_setLaneNat_self _ _ _ hp60 (degBitIdx_lt_6 _)]
      change ((getLaneNat st p) &&& (31 ^^^ condMaskNat m)).testBit (degBitIdx (cartDeg p)) = true
      rw [Nat.testBit_and, Nat.testBit_xor, h_match31.1 p hp1 hp2, testBit_31_degBitIdx, h_false]
      rfl
    · rw [testBit_getLaneNat_setLaneNat_ne _ _ _ p hp60 hpv (degBitIdx_lt_6 _)]
      exact h_match31.1 p hp1 hp2
  · intro p hp1 hp2
    have hp60 : p < 60 := by omega
    change getLaneNat (setLaneNat st v (getLaneNat st v &&& Nat.xor 31 (condMaskNat m))) p ≤ 31
    by_cases hpv : p = v
    · subst hpv
      have h_le : getLaneNat st p &&& Nat.xor 31 (condMaskNat m) ≤ 31 :=
        Nat.le_trans Nat.and_le_left (h_match31.2 p hp1 hp2)
      rw [getLaneNat_setLaneNat_self st p (getLaneNat st p &&& Nat.xor 31 (condMaskNat m)) hp60 (by omega)]
      exact h_le
    · rw [getLaneNat_setLaneNat_ne st v (getLaneNat st v &&& Nat.xor 31 (condMaskNat m)) p hp60 hpv]
      exact h_match31.2 p hp1 hp2

/-- Master Top-Down Traversal Soundness of `verifyTreePureRec` (Eliminating `ProofTree.sym`):
    Tracks the three invariants (`SymTableSound`, `SiblingSound`, `PrefixSound`) across
    both branches of every `ProofTree.cond` node, proving that every `ProofTree.sym` leaf
    reduces to a previously verified `CoreCartLeaf` subtree via dihedral symmetry. -/
theorem verifyTreePureRec_sound_of_pred (deg : Nat) (shiftedTable : List (List FastPosOut))
    (P : (Nat → Nat) → Prop)
    (h_deg1 : 1 ≤ deg) (h_deg : deg ≤ 11)
    (h_table : ∀ row ∈ shiftedTable, ∀ po ∈ row, validFastPosOut deg po = true)
    (h_leaf : ∀ cd, CoreCartLeaf deg shiftedTable cd → P cd)
    (h_sym : ∀ (cd : Nat → Nat) (k : Nat) (refl : Bool) (conds : List (Nat × Nat)),
      k < deg →
      (∀ c ∈ conds, 1 ≤ c.1 ∧ c.1 ≤ 2 * deg) →
      (∀ c ∈ conds, c.2.testBit (degBitIdx (symCartDeg deg k refl cd c.1)) = true) →
      (∀ cd', (∀ c ∈ conds, c.2.testBit (degBitIdx (cd' c.1)) = true) → P cd') →
      P cd)
    (t : ProofTree) :
    ∀ (maxLev st lineno lev condV condM : Nat) (syms : List SymOutlet) (hs : HintStream),
      validProofTree deg maxLev t = true →
      lev + maxLev < 60 →
      (∀ o ∈ syms, (∀ c ∈ o.conds, 1 ≤ c.1 ∧ c.1 ≤ 2 * deg) ∧
        (∀ cd', (∀ c ∈ o.conds, c.2.testBit (degBitIdx (cd' c.1)) = true) → P cd')) →
      (∀ conds, extractCondsRec deg condV condM lev = some conds →
        ∀ cd', (∀ c ∈ conds, c.2.testBit (degBitIdx (cd' c.1)) = true) → P cd') →
      (∀ cd', SatisfiesPrefix cd' condV condM lev → P cd' ∨ MatchesCartState31 deg cd' st) →
      (verifyTreePureRec deg shiftedTable t st lineno lev condV condM syms hs).1 = true →
      ∀ cd, SatisfiesPrefix cd condV condM lev → P cd := by
  induction t with
  | reduce =>
    intro maxLev st lineno lev condV condM syms hs _ _ _ _ h_pref h_ok cd h_cd
    rcases h_pref cd h_cd with hP | h_match31
    · exact hP
    · change (let (ok, hs') := reduceAxleRec deg 64 [st] hs
              strictNat (Nat.add lineno 1) fun lineno' => (ok, lineno', hs')).1 = true at h_ok
      simp only [strictNat_eq] at h_ok
      exact h_leaf cd (Or.inl (reduceAxleRec_sound deg cd h_deg 64 [st] hs ⟨st, List.mem_cons_self, h_match31⟩ h_ok))
  | hubcap members =>
    intro maxLev st lineno lev condV condM syms hs h_valid _ _ _ h_pref h_ok cd h_cd
    have h_cover : validHubcapCover deg members = true := by
      cases maxLev <;> exact h_valid
    rcases h_pref cd h_cd with hP | h_match31
    · exact hP
    · change (let (ok, hs') := verifyHubcapMembersRec deg st shiftedTable members hs
              strictNat (Nat.add lineno 1) fun lineno' => (ok, lineno', hs')).1 = true at h_ok
      simp only [strictNat_eq] at h_ok
      rcases verifyHubcapMembersRec_sound31 deg cd h_deg st h_match31 shiftedTable h_table members hs h_ok with h_red | h_bounds
      · exact h_leaf cd (Or.inl h_red)
      · exact h_leaf cd (Or.inr ⟨members, h_cover, h_bounds⟩)
  | sym k eps lev_in line =>
    intro maxLev st lineno lev condV condM syms hs _ _ h_syms _ h_pref h_ok cd h_cd
    rcases h_pref cd h_cd with hP | h_match31
    · exact hP
    · change (let ok :=
                Bool.rec false
                  (match findSymOutletRec line syms with
                   | none => false
                   | some found =>
                     Bool.rec false
                       (symForcedRec st (Nat.add k 1) deg (!Nat.beq eps 0) found.conds)
                       (Nat.beq found.nolines (Nat.add lev_in 1)))
                  (!Nat.ble deg k && Nat.ble eps 1)
              strictNat (Nat.add lineno 1) fun lineno' => (ok, lineno', hs)).1 = true at h_ok
      simp only [strictNat_eq] at h_ok
      cases h_ke : (!Nat.ble deg k && Nat.ble eps 1) with
      | false =>
        rw [h_ke] at h_ok; dsimp at h_ok; contradiction
      | true =>
        rw [h_ke] at h_ok; dsimp at h_ok
        cases h_find : findSymOutletRec line syms with
        | none =>
          rw [h_find] at h_ok; contradiction
        | some found =>
          rw [h_find] at h_ok; dsimp at h_ok
          cases h_nl : Nat.beq found.nolines (Nat.add lev_in 1) with
          | false =>
            rw [h_nl] at h_ok; dsimp at h_ok; contradiction
          | true =>
            rw [h_nl] at h_ok; dsimp at h_ok
            rcases Bool.and_eq_true_iff.mp h_ke with ⟨hk_not, _⟩
            have hk_lt : k < deg :=
              Classical.byContradiction fun h_ge => by
                rw [Nat.ble_eq_true_of_le (by omega)] at hk_not
                contradiction
            have ⟨h_found_conds, h_found_P⟩ := h_syms found (findSymOutletRec_mem line syms h_find)
            have h_shift_lt : Nat.add k 1 - 1 < deg := by
              change (k + 1) - 1 < deg
              omega
            have h_forced := symForcedRec_sound deg cd st (Nat.add k 1) (!Nat.beq eps 0)
              found.conds h_deg1 h_shift_lt h_match31.1 h_found_conds h_ok
            exact h_sym cd k (!Nat.beq eps 0) found.conds hk_lt h_found_conds h_forced h_found_P
  | cond v m tTrue tFalse ihTrue ihFalse =>
    intro maxLev st lineno lev condV condM syms hs h_valid h_lev_max h_syms h_sib h_pref h_ok
    cases maxLev with
    | zero =>
      dsimp [validProofTree] at h_valid
      contradiction
    | succ maxLev' =>
      dsimp [validProofTree] at h_valid
      rcases Bool.and_eq_true_iff.mp h_valid with ⟨h_v123, h_val_false⟩
      rcases Bool.and_eq_true_iff.mp h_v123 with ⟨h_v12, h_val_true⟩
      rcases Bool.and_eq_true_iff.mp h_v12 with ⟨hv1_b, hv2_b⟩
      have hv1 : 1 ≤ v := Nat.le_of_ble_eq_true hv1_b
      have hv2 : v ≤ 5 * deg := Nat.le_of_ble_eq_true hv2_b
      have hv64 : v < 64 := by omega
      have h_lev1 : lev + 1 < 60 := by omega
      rw [verifyTreePureRec_cond_eq] at h_ok
      simp only [strictNat_eq] at h_ok
      let maskTrue := condMaskNat m
      let maskFalse := Nat.xor 31 maskTrue
      let curLane := getLaneNat st v
      let stTrue := setLaneNat st v (Nat.land curLane maskTrue)
      let stFalse := setLaneNat st v (Nat.land curLane maskFalse)
      let lev1 := Nat.add lev 1
      let lineno1 := Nat.add lineno 1
      let syms' :=
        match extractCondsRec deg condV condM lev with
        | none => syms
        | some conds => { number := lineno, nolines := lev1, conds := conds } :: syms
      have h_syms' : ∀ o ∈ syms', (∀ c ∈ o.conds, 1 ≤ c.1 ∧ c.1 ≤ 2 * deg) ∧
          (∀ cd', (∀ c ∈ o.conds, c.2.testBit (degBitIdx (cd' c.1)) = true) → P cd') := by
        dsimp [syms']
        cases h_ext : extractCondsRec deg condV condM lev with
        | none => exact h_syms
        | some conds =>
          intro o ho
          rcases List.mem_cons.mp ho with rfl | ho_tail
          · exact ⟨extractCondsRec_sound deg condV condM lev h_ext, h_sib conds h_ext⟩
          · exact h_syms o ho_tail
      let condV' := setLaneNat (setLaneNat condV lev v) lev1 0
      let condM' := setLaneNat (setLaneNat condM lev maskTrue) lev1 0
      let resTrue := verifyTreePureRec deg shiftedTable tTrue stTrue lineno1 lev1 condV' condM' syms' hs
      change (@Bool.rec (fun _ => Bool × Nat × HintStream) (false, resTrue.2.fst, resTrue.2.snd)
        (verifyTreePureRec deg shiftedTable tFalse stFalse resTrue.2.fst lev condV' condM' syms' resTrue.2.snd)
        resTrue.fst).fst = true at h_ok
      cases h_b : resTrue.fst with
      | false =>
        rw [h_b] at h_ok; dsimp at h_ok; contradiction
      | true =>
        rw [h_b] at h_ok; dsimp at h_ok
        have h_sib_true : ∀ conds, extractCondsRec deg condV' condM' lev1 = some conds →
            ∀ cd', (∀ c ∈ conds, c.2.testBit (degBitIdx (cd' c.1)) = true) → P cd' := by
          intro conds h_some
          have h_z : getLaneNat condV' lev1 = 0 :=
            getLaneNat_setLaneNat_self _ lev1 0 h_lev1 (by omega)
          rw [extractCondsRec_eq_none_of_getLaneNat_zero deg condV' condM' lev1 h_z] at h_some
          contradiction
        have h_pref_true : ∀ cd', SatisfiesPrefix cd' condV' condM' lev1 → P cd' ∨ MatchesCartState31 deg cd' stTrue := by
          intro cd' h_sat1
          rcases (satisfiesPrefix_cond_succ_iff cd' condV condM lev v maskTrue h_lev1 hv64).mp h_sat1 with ⟨h_sat0, h_tb⟩
          rcases h_pref cd' h_sat0 with hP | h_match31
          · exact Or.inl hP
          · exact Or.inr (matchesCartState31_cond_true deg cd' st v m h_deg h_match31 h_tb)
        have h_true_all : ∀ cd', SatisfiesPrefix cd' condV' condM' lev1 → P cd' :=
          ihTrue maxLev' stTrue lineno1 lev1 condV' condM' syms' hs
            h_val_true (by change (lev + 1) + maxLev' < 60; omega) h_syms' h_sib_true h_pref_true h_b
        have h_sib_false : ∀ conds, extractCondsRec deg condV' condM' lev = some conds →
            ∀ cd', (∀ c ∈ conds, c.2.testBit (degBitIdx (cd' c.1)) = true) → P cd' := by
          intro conds h_some cd' h_sat
          exact h_true_all cd' (satisfiesPrefix_of_extractCondsRec deg condV' condM' lev h_some cd' h_sat)
        have h_pref_false : ∀ cd', SatisfiesPrefix cd' condV' condM' lev → P cd' ∨ MatchesCartState31 deg cd' stFalse := by
          intro cd' h_sat0'
          have h_sat0 : SatisfiesPrefix cd' condV condM lev :=
            (satisfiesPrefix_cond_iff cd' condV condM lev v maskTrue h_lev1).mp h_sat0'
          rcases h_pref cd' h_sat0 with hP | h_match31
          · exact Or.inl hP
          · cases h_bit : maskTrue.testBit (degBitIdx (cd' v)) with
            | true =>
              have h_sat1 : SatisfiesPrefix cd' condV' condM' lev1 :=
                (satisfiesPrefix_cond_succ_iff cd' condV condM lev v maskTrue h_lev1 hv64).mpr ⟨h_sat0, h_bit⟩
              exact Or.inl (h_true_all cd' h_sat1)
            | false =>
              exact Or.inr (matchesCartState31_cond_false deg cd' st v m h_deg h_match31 h_bit)
        have h_false_all : ∀ cd', SatisfiesPrefix cd' condV' condM' lev → P cd' :=
          ihFalse maxLev' stFalse resTrue.2.fst lev condV' condM' syms' resTrue.2.snd
            h_val_false (by omega) h_syms' h_sib_false h_pref_false h_ok
        intro cd h_cd
        exact h_false_all cd ((satisfiesPrefix_cond_iff cd condV condM lev v maskTrue h_lev1).mpr h_cd)

/-- A family `ℱ : (Nat → Nat) → Prop` of cartwheel degree assignments at hub degree `deg`
    is closed under dihedral symmetries (`k < deg` rotations and `refl : Bool` reflections)
    on the first two rings (`1 ≤ p ≤ 2 * deg`). -/
def DihedralClosedFamily (deg : Nat) (ℱ : (Nat → Nat) → Prop) : Prop :=
  ∀ (cd : Nat → Nat) (k : Nat) (refl : Bool),
    k < deg → ℱ cd → ∃ cd', ℱ cd' ∧ ∀ p, 1 ≤ p → p ≤ 2 * deg → cd' p = symCartDeg deg k refl cd p

/-- Inductive dihedral orbit of a cartwheel degree assignment `cartDeg` at hub degree `deg`
    under rotational shifts (`k < deg`) and reflections (`refl : Bool`). -/
inductive InDihedralOrbit (deg : Nat) (cartDeg : Nat → Nat) : (Nat → Nat) → Prop
  | base : InDihedralOrbit deg cartDeg cartDeg
  | step {cd : Nat → Nat} (k : Nat) (refl : Bool) :
      k < deg → InDihedralOrbit deg cartDeg cd →
      InDihedralOrbit deg cartDeg (symCartDeg deg k refl cd)

theorem dihedralClosedFamily_inDihedralOrbit (deg : Nat) (cartDeg : Nat → Nat) :
    DihedralClosedFamily deg (InDihedralOrbit deg cartDeg) :=
  fun cd k refl hk h_in => ⟨symCartDeg deg k refl cd, .step k refl hk h_in, fun _ _ _ => rfl⟩

/-- Top-level `verifyTree` Core Soundness (with `ProofTree.sym` eliminated):
    for any dihedral-closed family `ℱ` of cartwheel degree assignments (`DihedralClosedFamily deg ℱ`)
    that is non-empty (`∃ cd₀, ℱ cd₀`), if `validProofTree deg 58 t = true` and
    `verifyTree configs deg A_low A_upp t outs = true` for `deg ∈ {7, 8, 9, 10, 11}`,
    then there exists a member `cd ∈ ℱ` satisfying the 2-way `CoreCartLeaf` certificate
    (`HasExactReducedAxle` or `validHubcapCover` LP bound). -/
theorem verifyTree_core_soundness (configs : List Configuration) (deg : Nat)
    (A_low A_upp : Array Nat) (t : ProofTree) (outs : Array Outlet)
    (ℱ : (Nat → Nat) → Prop) (h_closed : DihedralClosedFamily deg ℱ)
    {cd0 : Nat → Nat} (h_cd0 : ℱ cd0)
    (h_deg : deg = 7 ∨ deg = 8 ∨ deg = 9 ∨ deg = 10 ∨ deg = 11)
    (h_valid : validProofTree deg 58 t = true)
    (h_ver : verifyTree configs deg A_low A_upp t outs = true) :
    ∃ cd, ℱ cd ∧ CoreCartLeaf deg (getShiftedTableForDeg deg) cd := by
  have h_deg1 : 1 ≤ deg := by rcases h_deg with rfl | rfl | rfl | rfl | rfl <;> omega
  have h_le11 : deg ≤ 11 := by rcases h_deg with rfl | rfl | rfl | rfl | rfl <;> omega
  let shiftedTable := getShiftedTableForDeg deg
  let P : (Nat → Nat) → Prop := fun cd => ℱ cd → ∃ cd', ℱ cd' ∧ CoreCartLeaf deg shiftedTable cd'
  have h_leaf : ∀ cd, CoreCartLeaf deg shiftedTable cd → P cd :=
    fun cd h_core h_F => ⟨cd, h_F, h_core⟩
  have h_sym : ∀ (cd : Nat → Nat) (k : Nat) (refl : Bool) (conds : List (Nat × Nat)),
      k < deg →
      (∀ c ∈ conds, 1 ≤ c.1 ∧ c.1 ≤ 2 * deg) →
      (∀ c ∈ conds, c.2.testBit (degBitIdx (symCartDeg deg k refl cd c.1)) = true) →
      (∀ cd', (∀ c ∈ conds, c.2.testBit (degBitIdx (cd' c.1)) = true) → P cd') →
      P cd := by
    intro cd k refl conds hk h_conds h_forced h_all_P h_F
    rcases h_closed cd k refl hk h_F with ⟨cd', h_F', h_eq⟩
    have h_sat' : ∀ c ∈ conds, c.2.testBit (degBitIdx (cd' c.1)) = true := by
      intro c hc
      rcases h_conds c hc with ⟨hc1, hc2⟩
      rw [h_eq c.1 hc1 hc2]
      exact h_forced c hc
    exact h_all_P cd' h_sat' h_F'
  have h_syms0 : ∀ o ∈ ([] : List SymOutlet), (∀ c ∈ o.conds, 1 ≤ c.1 ∧ c.1 ≤ 2 * deg) ∧
      (∀ cd', (∀ c ∈ o.conds, c.2.testBit (degBitIdx (cd' c.1)) = true) → P cd') :=
    fun _ h => by cases h
  have h_sib0 : ∀ conds, extractCondsRec deg 0 0 0 = some conds →
      ∀ cd', (∀ c ∈ conds, c.2.testBit (degBitIdx (cd' c.1)) = true) → P cd' := by
    intro conds h_some
    rw [extractCondsRec_eq_none_of_getLaneNat_zero deg 0 0 0 rfl] at h_some
    contradiction
  have h_pref0 : ∀ cd', SatisfiesPrefix cd' 0 0 0 → P cd' ∨ MatchesCartState31 deg cd' (getInitStateForDeg deg) :=
    fun cd' _ => Or.inr (matchesCartState31_getInitStateForDeg deg cd' h_deg)
  have h_sat0 : SatisfiesPrefix cd0 0 0 0 := fun _ hi => by omega
  exact verifyTreePureRec_sound_of_pred deg shiftedTable P h_deg1 h_le11
    (validFastPosOut_getShiftedTableForDeg deg h_deg) h_leaf h_sym t
    58 (getInitStateForDeg deg) 2 0 0 0 [] ([], getHintsForDeg deg)
    h_valid (by omega) h_syms0 h_sib0 h_pref0 h_ver cd0 h_sat0 h_cd0

/-- Top-level `DischargingTreesVerified` Core Soundness (with `ProofTree.sym` eliminated):
    for every hub degree `deg ∈ {7, 8, 9, 10, 11}` and any dihedral-closed family `ℱ`
    containing `cd0`, `DischargingTreesVerified configs` guarantees that some `cd ∈ ℱ`
    satisfies the non-vacuous 2-way `CoreCartLeaf deg (getShiftedTableForDeg deg) cd`. -/
theorem dischargingTreesVerified_core_soundness (configs : List Configuration)
    (h_trees : DischargingTreesVerified configs) (deg : Nat)
    (ℱ : (Nat → Nat) → Prop) (h_closed : DihedralClosedFamily deg ℱ)
    {cd0 : Nat → Nat} (h_cd0 : ℱ cd0)
    (h_deg : deg = 7 ∨ deg = 8 ∨ deg = 9 ∨ deg = 10 ∨ deg = 11) :
    ∃ cd, ℱ cd ∧ CoreCartLeaf deg (getShiftedTableForDeg deg) cd := by
  rcases h_trees with ⟨h7, h8, h9, h10, h11⟩
  rcases h_deg with rfl | rfl | rfl | rfl | rfl
  · exact verifyTree_core_soundness configs 7 (trivial_A_low 7) (trivial_A_upp 7) (present7 ()) (readOutlets 7 theRules) ℱ h_closed h_cd0 (Or.inl rfl) validProofTree_present7 h7
  · exact verifyTree_core_soundness configs 8 (trivial_A_low 8) (trivial_A_upp 8) (present8 ()) (readOutlets 8 theRules) ℱ h_closed h_cd0 (Or.inr (Or.inl rfl)) validProofTree_present8 h8
  · exact verifyTree_core_soundness configs 9 (trivial_A_low 9) (trivial_A_upp 9) (present9 ()) (readOutlets 9 theRules) ℱ h_closed h_cd0 (Or.inr (Or.inr (Or.inl rfl))) validProofTree_present9 h9
  · exact verifyTree_core_soundness configs 10 (trivial_A_low 10) (trivial_A_upp 10) (present10 ()) (readOutlets 10 theRules) ℱ h_closed h_cd0 (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) validProofTree_present10 h10
  · exact verifyTree_core_soundness configs 11 (trivial_A_low 11) (trivial_A_upp 11) (present11 ()) (readOutlets 11 theRules) ℱ h_closed h_cd0 (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) validProofTree_present11 h11

/-- Dihedral Orbit Core Soundness for any cartwheel degree assignment `cartDeg : Nat → Nat`:
    `DischargingTreesVerified configs` guarantees that some member `cd ∈ InDihedralOrbit deg cartDeg`
    satisfies `CoreCartLeaf deg (getShiftedTableForDeg deg) cd` (and hence either `HasExactReducedAxle`
    or `10 * (6 - deg) + ∑_{i=1..deg} activeOutletSum(i) ≤ 0`). -/
theorem dischargingTreesVerified_orbit_core_soundness (configs : List Configuration)
    (h_trees : DischargingTreesVerified configs) (deg : Nat) (cartDeg : Nat → Nat)
    (h_deg : deg = 7 ∨ deg = 8 ∨ deg = 9 ∨ deg = 10 ∨ deg = 11) :
    ∃ cd, InDihedralOrbit deg cartDeg cd ∧ CoreCartLeaf deg (getShiftedTableForDeg deg) cd :=
  dischargingTreesVerified_core_soundness configs h_trees deg
    (InDihedralOrbit deg cartDeg) (dihedralClosedFamily_inDihedralOrbit deg cartDeg)
    InDihedralOrbit.base h_deg

/-- Orientation-aware `i`-th spoke dart (`1 ≤ i ≤ deg`) around hub dart `d0` in hypermap `H`:
    iterates `H.node.f` when `refl = false` and `H.node.inv` (`H.node.symm`) when `refl = true`. -/
def spokeDartOriented (H : Hypermap) (refl : Bool) (d0 : H.Dart) (i : Nat) : H.Dart :=
  if refl then Hypermap.Perm.iter H.node.symm (i - 1) d0
  else Hypermap.Perm.iter H.node (i - 1) d0

/-- Orientation-aware cartwheel position map `0 ≤ p ≤ 5 * deg` around hub dart `d0` in hypermap `H`. -/
def cartDartOriented (H : Hypermap) (deg : Nat) (refl : Bool) (d0 : H.Dart) (p : Nat) : H.Dart :=
  if p == 0 then d0
  else
    let ringIdx := (p - 1) / deg
    let s := spokeDartOriented H refl d0 ((p - 1) % deg + 1)
    if ringIdx == 0 then ruleVertexDart H (!refl) (H.edge.f s) 0
    else if ringIdx == 1 then ruleVertexDart H (!refl) (H.edge.f s) 5
    else if ringIdx == 2 then ruleVertexDart H (!refl) (H.edge.f s) 12
    else if ringIdx == 3 then ruleVertexDart H (!refl) (H.edge.f s) 13
    else if refl then H.edge.f (H.node.inv (H.node.inv (H.node.inv (H.node.inv (H.node.inv (H.edge.f s))))))
    else H.edge.f (H.node.f (H.node.f (H.node.f (H.node.f (H.node.f (H.edge.f s))))))

/-- Orientation-aware cartwheel degree assignment `Nat → Nat` around hub dart `d0` in hypermap `H`. -/
def cartDegOriented (H : Hypermap) [DecidableEq H.Dart] (fuel deg : Nat) (refl : Bool) (d0 : H.Dart) (p : Nat) : Nat :=
  Hypermap.nodeDegree H (cartDartOriented H deg refl d0 p) fuel

@[simp] theorem spokeDartOriented_false (H : Hypermap) (d0 : H.Dart) (i : Nat) :
    spokeDartOriented H false d0 i = spokeDart H d0 i := rfl

@[simp] theorem cartDartOriented_false (H : Hypermap) (deg : Nat) (d0 : H.Dart) (p : Nat) :
    cartDartOriented H deg false d0 p = cartDart H deg d0 p := rfl

@[simp] theorem cartDegOriented_false (H : Hypermap) [DecidableEq H.Dart] (fuel deg : Nat) (d0 : H.Dart) (p : Nat) :
    cartDegOriented H fuel deg false d0 p = cartDegOfDart H fuel deg d0 p := rfl

@[simp] theorem cartDartOriented_zero (H : Hypermap) (deg : Nat) (refl : Bool) (d0 : H.Dart) :
    cartDartOriented H deg refl d0 0 = d0 := rfl

@[simp] theorem cartDegOriented_zero (H : Hypermap) [DecidableEq H.Dart] (fuel deg : Nat) (refl : Bool) (d0 : H.Dart) :
    cartDegOriented H fuel deg refl d0 0 = Hypermap.nodeDegree H d0 fuel := rfl

theorem cartDartOriented_spoke (H : Hypermap) (deg : Nat) (refl : Bool) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi2 : i ≤ deg) :
    cartDartOriented H deg refl d0 i = H.edge.f (spokeDartOriented H refl d0 i) := by
  dsimp [cartDartOriented]
  have h_ne0 : (i == 0) = false := beq_false_of_ne (by omega)
  have h_div : (i - 1) / deg = 0 := by simpa using ringIdx_of_mul_add (k := 0) hi1 hi2
  have h_mod : (i - 1) % deg + 1 = i := by simpa using spokeIdx_of_mul_add (k := 0) hi1 hi2
  rw [h_ne0, h_div, h_mod]
  rfl

theorem cartDartOriented_hat (H : Hypermap) (deg : Nat) (refl : Bool) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi2 : i ≤ deg) :
    cartDartOriented H deg refl d0 (deg + i) =
      ruleVertexDart H (!refl) (H.edge.f (spokeDartOriented H refl d0 i)) 5 := by
  dsimp [cartDartOriented]
  have h_ne0 : (deg + i == 0) = false := beq_false_of_ne (by omega)
  have h_div : ((deg + i) - 1) / deg = 1 := by simpa using ringIdx_of_mul_add (k := 1) hi1 hi2
  have h_mod : ((deg + i) - 1) % deg + 1 = i := by simpa using spokeIdx_of_mul_add (k := 1) hi1 hi2
  rw [h_ne0, h_div, h_mod]
  rfl

theorem cartDartOriented_fan1 (H : Hypermap) (deg : Nat) (refl : Bool) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi2 : i ≤ deg) :
    cartDartOriented H deg refl d0 (2 * deg + i) =
      ruleVertexDart H (!refl) (H.edge.f (spokeDartOriented H refl d0 i)) 12 := by
  dsimp [cartDartOriented]
  have h_ne0 : (2 * deg + i == 0) = false := beq_false_of_ne (by omega)
  have h_div : ((2 * deg + i) - 1) / deg = 2 := ringIdx_of_mul_add (k := 2) hi1 hi2
  have h_mod : ((2 * deg + i) - 1) % deg + 1 = i := spokeIdx_of_mul_add (k := 2) hi1 hi2
  rw [h_ne0, h_div, h_mod]
  rfl

theorem cartDartOriented_fan2 (H : Hypermap) (deg : Nat) (refl : Bool) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi2 : i ≤ deg) :
    cartDartOriented H deg refl d0 (3 * deg + i) =
      ruleVertexDart H (!refl) (H.edge.f (spokeDartOriented H refl d0 i)) 13 := by
  dsimp [cartDartOriented]
  have h_ne0 : (3 * deg + i == 0) = false := beq_false_of_ne (by omega)
  have h_div : ((3 * deg + i) - 1) / deg = 3 := ringIdx_of_mul_add (k := 3) hi1 hi2
  have h_mod : ((3 * deg + i) - 1) % deg + 1 = i := spokeIdx_of_mul_add (k := 3) hi1 hi2
  rw [h_ne0, h_div, h_mod]
  rfl

theorem cartDartOriented_fan3 (H : Hypermap) (deg : Nat) (refl : Bool) (d0 : H.Dart) {i : Nat}
    (hi1 : 1 ≤ i) (hi2 : i ≤ deg) :
    cartDartOriented H deg refl d0 (4 * deg + i) =
      if refl then H.edge.f (H.node.inv (H.node.inv (H.node.inv (H.node.inv (H.node.inv (H.edge.f (spokeDartOriented H refl d0 i)))))))
      else H.edge.f (H.node.f (H.node.f (H.node.f (H.node.f (H.node.f (H.edge.f (spokeDartOriented H refl d0 i))))))) := by
  dsimp [cartDartOriented]
  have h_ne0 : (4 * deg + i == 0) = false := beq_false_of_ne (by omega)
  have h_div : ((4 * deg + i) - 1) / deg = 4 := ringIdx_of_mul_add (k := 4) hi1 hi2
  have h_mod : ((4 * deg + i) - 1) % deg + 1 = i := spokeIdx_of_mul_add (k := 4) hi1 hi2
  rw [h_ne0, h_div, h_mod]
  rfl

/-!
### Stage N.1: Triangulation Face-Step & Hat-Reflection Identities
-/

/-- `H.face.f d = H.node.inv (H.edge.f d)`. -/
theorem face_f_eq_node_inv_edge_f (H : Hypermap) (d : H.Dart) :
    H.face.f d = H.node.inv (H.edge.f d) := by
  rw [Hypermap.face_eq_node_inv_edge_inv, Hypermap.edge_inv_eq_edge]

/-- On a complete dart list (`darts.length ≤ fuel`), `Hypermap.faceDegree H d fuel = 3`
    implies `H.face.f (H.face.f (H.face.f d)) = d`. -/
theorem face_f_three_of_faceDegree_eq_three (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {d : H.Dart}
    (h_tri : Hypermap.faceDegree H d fuel = 3) :
    H.face.f (H.face.f (H.face.f d)) = d := by
  have h_per := Hypermap.perm_iter_length_getOrbit_eq_self_of_complete H.face darts h_all h_le d
  change Hypermap.Perm.iter H.face (Hypermap.faceDegree H d fuel) d = d at h_per
  rw [h_tri] at h_per
  exact h_per

/-- Fundamental Triangulation Face-Step Identity:
    if `H.face.f^3 = id` at `H.edge.f (H.node.f s)`, then
    `H.edge.f (H.node.inv (H.edge.f s)) = H.node.f (H.edge.f (H.node.f s))`. -/
theorem edge_node_inv_edge_eq_node_f_edge_node_f (H : Hypermap)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x) (s : H.Dart) :
    H.edge.f (H.node.inv (H.edge.f s)) = H.node.f (H.edge.f (H.node.f s)) := by
  have h_fen := Hypermap.face_edge_node_id H s
  have h_ff : H.face.f (H.face.f s) = H.edge.f (H.node.f s) := by
    have h1 := congrArg (fun x => H.face.f (H.face.f x)) h_fen
    dsimp at h1
    rw [h_tri3 (H.edge.f (H.node.f s))] at h1
    exact h1.symm
  rw [face_f_eq_node_inv_edge_f, face_f_eq_node_inv_edge_f] at h_ff
  have h2 := congrArg H.node.f h_ff
  rw [H.node.right_inv] at h2
  exact h2

/-- Triangulation Hat-Reflection Dart Identity:
    if `H.face.f^3 = id` everywhere on `H`, then for every spoke dart `s : H.Dart`,
    `ruleVertexDart H true (H.edge.f s) 5 = H.node.f (ruleVertexDart H false (H.edge.f (H.node.f s)) 5)`. -/
theorem hat_dart_true_eq_node_f_false (H : Hypermap)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x) (s : H.Dart) :
    ruleVertexDart H true (H.edge.f s) 5 =
      H.node.f (ruleVertexDart H false (H.edge.f (H.node.f s)) 5) := by
  dsimp [ruleVertexDart, ruleRot]
  let y := H.node.f (H.edge.f (H.node.f s))
  have h1 : H.node.inv (H.edge.f s) = H.edge.f y := by
    have h_step := edge_node_inv_edge_eq_node_f_edge_node_f H h_tri3 s
    have h_e := congrArg H.edge.f h_step
    rw [H.edge_involution] at h_e
    exact h_e
  rw [h1]
  exact edge_node_inv_edge_eq_node_f_edge_node_f H h_tri3 y

/-- Inverse form of the Triangulation Hat-Reflection Dart Identity:
    `H.node.inv (ruleVertexDart H true (H.edge.f s) 5) = ruleVertexDart H false (H.edge.f (H.node.f s)) 5`. -/
theorem node_inv_hat_dart_true_eq_false (H : Hypermap)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x) (s : H.Dart) :
    H.node.inv (ruleVertexDart H true (H.edge.f s) 5) =
      ruleVertexDart H false (H.edge.f (H.node.f s)) 5 := by
  rw [hat_dart_true_eq_node_f_false H h_tri3 s, H.node.left_inv]

/-- On a complete dart list (`darts.length ≤ fuel`), `H.node.f d` and `d` have the same `nodeDegree`. -/
theorem nodeDegree_node_f_eq_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (d : H.Dart) :
    Hypermap.nodeDegree H (H.node.f d) fuel = Hypermap.nodeDegree H d fuel := by
  have hd_mem : d ∈ getOrbit H.node fuel d :=
    List.contains_iff_mem.mp (Hypermap.getOrbit_contains_self H.node fuel d)
  have hfd_mem : H.node.f d ∈ getOrbit H.node fuel d :=
    Hypermap.getOrbit_closed_under_f_of_complete H.node darts h_all h_le hd_mem
  exact nodeDegree_eq_of_mem_getOrbit H darts h_all h_le hfd_mem

/-- Unified Triangulation Hat-Reflection Degree Identity:
    for any orientation `r0 : Bool` and spoke dart `s : H.Dart` on a complete triangulated hypermap,
    `nodeDegree` at `ruleVertexDart H (!r0) (H.edge.f s) 5` equals
    `nodeDegree` at `ruleVertexDart H r0 (H.edge.f (ruleRot H r0 s)) 5`. -/
theorem nodeDegree_hat_refl_eq_of_triangulation (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    (r0 : Bool) (s : H.Dart) :
    Hypermap.nodeDegree H (ruleVertexDart H (!r0) (H.edge.f s) 5) fuel =
      Hypermap.nodeDegree H (ruleVertexDart H r0 (H.edge.f (ruleRot H r0 s)) 5) fuel := by
  cases r0 with
  | false =>
    change Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f s) 5) fuel =
      Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f (H.node.f s)) 5) fuel
    rw [hat_dart_true_eq_node_f_false H h_tri3 s]
    exact nodeDegree_node_f_eq_of_complete H darts h_all h_le _
  | true =>
    change Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f s) 5) fuel =
      Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f (H.node.inv s)) 5) fuel
    have h_eq := hat_dart_true_eq_node_f_false H h_tri3 (H.node.inv s)
    rw [H.node.right_inv] at h_eq
    rw [h_eq]
    exact (nodeDegree_node_f_eq_of_complete H darts h_all h_le _).symm

/-!
### Stage N.2: Pure `RealHypermapHubFamily` Dihedral Closure & Spoke-Sum Decomposition of `orbitNetShift`
-/

/-- Orientation-selected vertex permutation (`H.node` for `refl = false`, `H.node.symm` for `refl = true`). -/
def nodePermOriented (H : Hypermap) (refl : Bool) : Perm H.Dart :=
  if refl then H.node.symm else H.node

theorem spokeDartOriented_eq_iter (H : Hypermap) (refl : Bool) (d0 : H.Dart) (i : Nat) :
    spokeDartOriented H refl d0 i = Hypermap.Perm.iter (nodePermOriented H refl) (i - 1) d0 := by
  cases refl <;> rfl

theorem ruleRot_eq_nodePermOriented_f (H : Hypermap) (refl : Bool) (d : H.Dart) :
    ruleRot H refl d = (nodePermOriented H refl).f d := by
  cases refl <;> rfl

theorem perm_iter_nodePermOriented_not (H : Hypermap) (refl : Bool) (m : Nat) (d : H.Dart) :
    Hypermap.Perm.iter (nodePermOriented H (!refl)) m d =
      Hypermap.Perm.iter (nodePermOriented H refl).symm m d := by
  cases refl <;> rfl

theorem perm_iter_symm_of_iter {D : Type} (q : Perm D) {m n : Nat} (hm : m ≤ n) (x : D) :
    Hypermap.Perm.iter q.symm m (Hypermap.Perm.iter q n x) =
      Hypermap.Perm.iter q (n - m) x := by
  have h_it := Hypermap.Perm.iter_add q m (n - m) x
  rw [Nat.add_sub_of_le hm] at h_it
  rw [h_it]
  exact Hypermap.Perm.iter_symm_left_inv q m (Hypermap.Perm.iter q (n - m) x)

theorem perm_iter_nodePermOriented_mem_getOrbit_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u d0 : H.Dart}
    (hd0 : d0 ∈ getOrbit H.node fuel u) (refl : Bool) (n : Nat) :
    Hypermap.Perm.iter (nodePermOriented H refl) n d0 ∈ getOrbit H.node fuel u := by
  induction n with
  | zero => exact hd0
  | succ n ih =>
    rw [Hypermap.Perm.iter_succ]
    cases refl with
    | false =>
      exact Hypermap.getOrbit_closed_under_f_of_complete H.node darts h_all h_le ih
    | true =>
      exact Hypermap.getOrbit_closed_under_inv_of_complete H.node darts h_all h_le ih

/-- If `d0 ∈ getOrbit H.node fuel u`, then every oriented spoke `spokeDartOriented H refl d0 i`
    also belongs to `getOrbit H.node fuel u`. -/
theorem spokeDartOriented_mem_getOrbit_of_complete (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u d0 : H.Dart}
    (hd0 : d0 ∈ getOrbit H.node fuel u) (refl : Bool) (i : Nat) :
    spokeDartOriented H refl d0 i ∈ getOrbit H.node fuel u := by
  rw [spokeDartOriented_eq_iter]
  exact perm_iter_nodePermOriented_mem_getOrbit_of_complete H darts h_all h_le hd0 refl (i - 1)

/-- Periodicity of `nodePermOriented H refl` on any dart `d0 ∈ getOrbit H.node fuel u`
    of degree `deg = Hypermap.nodeDegree H u fuel`. -/
theorem perm_iter_nodePermOriented_deg_eq_self (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u d0 : H.Dart}
    (hd0 : d0 ∈ getOrbit H.node fuel u) (refl : Bool) :
    Hypermap.Perm.iter (nodePermOriented H refl) (Hypermap.nodeDegree H u fuel) d0 = d0 := by
  have h_closes_u := Hypermap.orbitClosesWithin_mono H.node u u
    (Hypermap.orbitClosesWithin_of_complete H.node darts h_all u) h_le
  have h_len : (getOrbit H.node fuel d0).length = Hypermap.nodeDegree H u fuel :=
    Hypermap.getOrbit_length_eq_of_mem H.node fuel h_closes_u hd0
  rw [← h_len]
  cases refl with
  | false =>
    exact Hypermap.perm_iter_length_getOrbit_eq_self_of_complete H.node darts h_all h_le d0
  | true =>
    exact Hypermap.perm_iter_symm_length_getOrbit_eq_self_of_complete H.node darts h_all h_le d0

/-- Rotational shift of `spokeDartOriented`: shifting spoke index `i ∈ 1..deg` by `k < deg`
    around `d0` is identical to taking spoke `i` around `spokeDartOriented H refl d0 (k + 1)`. -/
theorem spokeDartOriented_shiftCartPos_eq (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u d0 : H.Dart}
    (hd0 : d0 ∈ getOrbit H.node fuel u) (refl : Bool)
    (k : Nat) {i : Nat}
    (hi1 : 1 ≤ i) (hi2 : i ≤ Hypermap.nodeDegree H u fuel) :
    let deg := Hypermap.nodeDegree H u fuel
    spokeDartOriented H refl (spokeDartOriented H refl d0 (k + 1)) i =
      spokeDartOriented H refl d0 (shiftCartPos deg k i) := by
  intro deg0
  rw [spokeDartOriented_eq_iter, spokeDartOriented_eq_iter, spokeDartOriented_eq_iter]
  have hk_sub : k + 1 - 1 = k := by omega
  rw [hk_sub, ← Hypermap.Perm.iter_add]
  unfold shiftCartPos
  have h_mod : Nat.mod (Nat.sub i 1) deg0 = i - 1 := by
    change (i - 1) % deg0 = i - 1
    exact Nat.mod_eq_of_lt (by omega)
  rw [h_mod]
  cases h_ble : Nat.ble deg0 (Nat.add k (i - 1)) with
  | false =>
    dsimp
    have h_eq : i + k - 1 = i - 1 + k := by omega
    rw [h_eq]
  | true =>
    dsimp
    have h_ge : deg0 ≤ k + (i - 1) := Nat.le_of_ble_eq_true h_ble
    have h_per : Hypermap.Perm.iter (nodePermOriented H refl) deg0 d0 = d0 :=
      perm_iter_nodePermOriented_deg_eq_self H darts h_all h_le hd0 refl
    have h_split : i - 1 + k = (i + k - deg0 - 1) + deg0 := by omega
    rw [h_split, Hypermap.Perm.iter_add, h_per]

/-- `shiftCartPos deg k (ringIdx * deg + i)` preserves the ring index `ringIdx` and shifts the spoke `i`. -/
theorem shiftCartPos_mul_add {deg k ringIdx i : Nat} (hi1 : 1 ≤ i) (hi2 : i ≤ deg) :
    shiftCartPos deg k (ringIdx * deg + i) = ringIdx * deg + shiftCartPos deg k i := by
  unfold shiftCartPos
  have h_mod1 : Nat.mod (Nat.sub (ringIdx * deg + i) 1) deg = i - 1 := by
    have h := spokeIdx_of_mul_add (deg := deg) (k := ringIdx) (i := i) hi1 hi2
    change (ringIdx * deg + i - 1) % deg = i - 1
    omega
  have h_mod2 : Nat.mod (Nat.sub i 1) deg = i - 1 := by
    change (i - 1) % deg = i - 1
    exact Nat.mod_eq_of_lt (by omega)
  rw [h_mod1, h_mod2]
  cases h_ble : Nat.ble deg (Nat.add k (i - 1)) with
  | false =>
    dsimp
    change ringIdx * deg + i + k = ringIdx * deg + (i + k)
    omega
  | true =>
    dsimp
    have h_ge : deg ≤ k + (i - 1) := Nat.le_of_ble_eq_true h_ble
    change ringIdx * deg + i + k - deg = ringIdx * deg + (i + k - deg)
    omega

/-- Rotational shift of `cartDartOriented`: for any `1 ≤ p ≤ 5 * deg`, shifting `p` by `k < deg`
    around `d0` gives the exact same dart as `p` around `spokeDartOriented H refl d0 (k + 1)`. -/
theorem cartDartOriented_shiftCartPos_eq (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u d0 : H.Dart}
    (hd0 : d0 ∈ getOrbit H.node fuel u) (refl : Bool)
    {k p : Nat} (hk : k < Hypermap.nodeDegree H u fuel) (hp1 : 1 ≤ p) :
    let deg := Hypermap.nodeDegree H u fuel
    cartDartOriented H deg refl (spokeDartOriented H refl d0 (k + 1)) p =
      cartDartOriented H deg refl d0 (shiftCartPos deg k p) := by
  intro deg0
  have h_deg_pos : 1 ≤ deg0 := by omega
  let ringIdx := (p - 1) / deg0
  let i := (p - 1) % deg0 + 1
  have hi1 : 1 ≤ i := by omega
  have hi2 : i ≤ deg0 := by
    have := Nat.mod_lt (p - 1) (by omega : 0 < deg0)
    omega
  have hp_eq : p = ringIdx * deg0 + i := by
    have h_dm := Nat.div_add_mod (p - 1) deg0
    dsimp [ringIdx, i]
    rw [Nat.mul_comm]
    omega
  have h_sh_eq : shiftCartPos deg0 k p = ringIdx * deg0 + shiftCartPos deg0 k i := by
    conv => lhs; rw [hp_eq]
    exact shiftCartPos_mul_add hi1 hi2
  have h_sh_bnds := shiftCartPos_bounds h_deg_pos hk hi1 (by omega : i ≤ 2 * deg0)
  have h_sh_i_le : shiftCartPos deg0 k i ≤ deg0 := by
    unfold shiftCartPos
    have h_mod : Nat.mod (Nat.sub i 1) deg0 = i - 1 := by
      change (i - 1) % deg0 = i - 1
      exact Nat.mod_eq_of_lt (by omega)
    rw [h_mod]
    cases h_ble : Nat.ble deg0 (Nat.add k (i - 1)) with
    | false =>
      dsimp
      have h_lt : k + (i - 1) < deg0 := by
        cases Classical.em (deg0 ≤ k + (i - 1)) with
        | inl h_ge =>
          have h_tr : Nat.ble deg0 (Nat.add k (i - 1)) = true := Nat.ble_eq_true_of_le h_ge
          rw [h_ble] at h_tr; contradiction
        | inr h_lt => omega
      change i + k ≤ deg0
      omega
    | true =>
      dsimp
      change i + k - deg0 ≤ deg0
      omega
  have h_sh_pos : 1 ≤ shiftCartPos deg0 k p := by
    rw [h_sh_eq]
    have := h_sh_bnds.1
    omega
  dsimp [cartDartOriented]
  have hp0 : (p == 0) = false := beq_false_of_ne (by omega)
  have hshp0 : (shiftCartPos deg0 k p == 0) = false := beq_false_of_ne (by omega)
  have h_div_sh : (shiftCartPos deg0 k p - 1) / deg0 = ringIdx := by
    rw [h_sh_eq]
    exact ringIdx_of_mul_add h_sh_bnds.1 h_sh_i_le
  have h_mod_sh : (shiftCartPos deg0 k p - 1) % deg0 + 1 = shiftCartPos deg0 k i := by
    rw [h_sh_eq]
    exact spokeIdx_of_mul_add h_sh_bnds.1 h_sh_i_le
  rw [hp0, hshp0, h_div_sh, h_mod_sh]
  dsimp
  have h_spk : spokeDartOriented H refl (spokeDartOriented H refl d0 (k + 1)) i =
      spokeDartOriented H refl d0 (shiftCartPos deg0 k i) :=
    spokeDartOriented_shiftCartPos_eq H darts h_all h_le hd0 refl k hi1 hi2
  rw [show (p - 1) % deg0 + 1 = i from rfl, h_spk]

/-- Reflectional invariance of `cartDegOriented` on `1 ≤ p ≤ 2 * deg` for any triangulated hypermap:
    reflecting `(r0, d1)` via `reflCartPos deg p` agrees with `(!r0, spokeDartOriented H r0 d1 deg)`. -/
theorem cartDegOriented_reflCartPos_eq (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x)
    {u d1 : H.Dart} (hd1 : d1 ∈ getOrbit H.node fuel u) (r0 : Bool)
    {p : Nat} (h_deg : 1 ≤ Hypermap.nodeDegree H u fuel)
    (hp1 : 1 ≤ p) (hp2 : p ≤ 2 * Hypermap.nodeDegree H u fuel) :
    let deg := Hypermap.nodeDegree H u fuel
    cartDegOriented H fuel deg (!r0) (spokeDartOriented H r0 d1 deg) p =
      cartDegOriented H fuel deg r0 d1 (reflCartPos deg p) := by
  intro deg0
  let d2 := spokeDartOriented H r0 d1 deg0
  have h_spk_d2 : ∀ i, 1 ≤ i → i ≤ deg0 →
      spokeDartOriented H (!r0) d2 i =
        Hypermap.Perm.iter (nodePermOriented H r0) (deg0 - i) d1 := by
    intro i hi1 hi2
    dsimp [d2]
    rw [spokeDartOriented_eq_iter, spokeDartOriented_eq_iter, perm_iter_nodePermOriented_not]
    have h_le_deg : i - 1 ≤ deg0 - 1 := by omega
    rw [perm_iter_symm_of_iter (nodePermOriented H r0) h_le_deg d1]
    have h_sub_eq : deg0 - 1 - (i - 1) = deg0 - i := by omega
    rw [h_sub_eq]
  by_cases hp_le : p ≤ deg0
  · -- Case 1: Spokes (`1 ≤ p ≤ deg0`)
    have h_refl_p : reflCartPos deg0 p = deg0 - p + 1 := by
      unfold reflCartPos
      have h_ble : Nat.ble p deg0 = true := Nat.ble_eq_true_of_le hp_le
      rw [h_ble]
      rfl
    rw [h_refl_p]
    dsimp [cartDegOriented]
    rw [cartDartOriented_spoke H deg0 (!r0) d2 hp1 hp_le,
        cartDartOriented_spoke H deg0 r0 d1 (by omega) (by omega),
        h_spk_d2 p hp1 hp_le, spokeDartOriented_eq_iter]
    have h_sub : deg0 - p + 1 - 1 = deg0 - p := by omega
    rw [h_sub]
  · -- Case 2: Hats (`deg0 + 1 ≤ p ≤ 2 * deg0`)
    let i := p - deg0
    have hi1 : 1 ≤ i := by omega
    have hi2 : i ≤ deg0 := by omega
    have hp_eq : p = deg0 + i := by omega
    by_cases hp_lt2 : p < 2 * deg0
    · -- Subcase 2a: Interior Hats (`1 ≤ i < deg0`)
      have hi_lt : i < deg0 := by omega
      have h_refl_p : reflCartPos deg0 p = deg0 + (deg0 - i) := by
        unfold reflCartPos
        have h_ble1 : Nat.ble p deg0 = false := by
          cases h : Nat.ble p deg0 with
          | false => rfl
          | true => have := Nat.le_of_ble_eq_true h; omega
        have h_ble2 : Nat.ble (Nat.mul 2 deg0) p = false := by
          cases h : Nat.ble (Nat.mul 2 deg0) p with
          | false => rfl
          | true =>
            have h_le2 : 2 * deg0 ≤ p := Nat.le_of_ble_eq_true h
            omega
        rw [h_ble1, h_ble2]
        dsimp
        change 3 * deg0 - p = deg0 + (deg0 - i)
        omega
      rw [h_refl_p, hp_eq]
      dsimp [cartDegOriented]
      rw [cartDartOriented_hat H deg0 (!r0) d2 hi1 hi2,
          cartDartOriented_hat H deg0 r0 d1 (by omega) (by omega),
          Bool.not_not, h_spk_d2 i hi1 hi2]
      have h_iter_step : Hypermap.Perm.iter (nodePermOriented H r0) (deg0 - i) d1 =
          ruleRot H r0 (spokeDartOriented H r0 d1 (deg0 - i)) := by
        rw [spokeDartOriented_eq_iter, ruleRot_eq_nodePermOriented_f, ← Hypermap.Perm.iter_succ]
        have h_s : deg0 - i - 1 + 1 = deg0 - i := by omega
        rw [h_s]
      rw [h_iter_step]
      exact (nodeDegree_hat_refl_eq_of_triangulation H darts h_all h_le h_tri3 r0 _).symm
    · -- Subcase 2b: Fixed Hat (`p = 2 * deg0`, `i = deg0`)
      have hp_2deg : p = 2 * deg0 := by omega
      have hi_deg : i = deg0 := by omega
      have h_refl_p : reflCartPos deg0 p = deg0 + deg0 := by
        unfold reflCartPos
        have h_ble1 : Nat.ble p deg0 = false := by
          cases h : Nat.ble p deg0 with
          | false => rfl
          | true => have := Nat.le_of_ble_eq_true h; omega
        have h_ble2 : Nat.ble (Nat.mul 2 deg0) p = true := by
          apply Nat.ble_eq_true_of_le
          change 2 * deg0 ≤ p
          omega
        rw [h_ble1, h_ble2]
        dsimp
        change 2 * deg0 = deg0 + deg0
        omega
      rw [h_refl_p, show p = deg0 + deg0 by omega]
      dsimp [cartDegOriented]
      rw [cartDartOriented_hat H deg0 (!r0) d2 h_deg (Nat.le_refl deg0),
          cartDartOriented_hat H deg0 r0 d1 h_deg (Nat.le_refl deg0),
          Bool.not_not, h_spk_d2 deg0 h_deg (Nat.le_refl deg0), Nat.sub_self]
      dsimp [Hypermap.Perm.iter]
      have h_per : Hypermap.Perm.iter (nodePermOriented H r0) deg0 d1 = d1 :=
        perm_iter_nodePermOriented_deg_eq_self H darts h_all h_le hd1 r0
      have h_d1_rot : d1 = ruleRot H r0 (spokeDartOriented H r0 d1 deg0) := by
        rw [spokeDartOriented_eq_iter, ruleRot_eq_nodePermOriented_f, ← Hypermap.Perm.iter_succ]
        have h_s : deg0 - 1 + 1 = deg0 := by omega
        rw [h_s, h_per]
      have h_lhs : Hypermap.nodeDegree H (ruleVertexDart H r0 (H.edge.f d1) 5) fuel =
          Hypermap.nodeDegree H (ruleVertexDart H r0 (H.edge.f (ruleRot H r0 (spokeDartOriented H r0 d1 deg0))) 5) fuel :=
        congrArg (fun x => Hypermap.nodeDegree H (ruleVertexDart H r0 (H.edge.f x) 5) fuel) h_d1_rot
      rw [h_lhs]
      exact (nodeDegree_hat_refl_eq_of_triangulation H darts h_all h_le h_tri3 r0 _).symm

/-- Pure Real-Hypermap Hub Family (`Zero` synthetic `.sym` constructors!):
    contains **only** genuine hypermap cartwheel degree functions `cartDegOriented H fuel deg refl d0`
    for `d0 ∈ getOrbit H.node fuel u` and `refl : Bool`. -/
def RealHypermapHubFamily (H : Hypermap) [DecidableEq H.Dart] (fuel deg : Nat) (u : H.Dart)
    (cd : Nat → Nat) : Prop :=
  ∃ d0 ∈ getOrbit H.node fuel u, ∃ refl : Bool,
    cd = cartDegOriented H fuel deg refl d0

/-- On any complete triangulated hypermap (`∀ d ∈ darts, Hypermap.faceDegree H d fuel = 3`),
    `RealHypermapHubFamily H fuel deg u` (`deg = Hypermap.nodeDegree H u fuel`) is unconditionally
    closed under the full dihedral group `DihedralClosedFamily deg`! -/
theorem dihedralClosedFamily_realHypermapHubFamily (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_tri : ∀ d ∈ darts, Hypermap.faceDegree H d fuel = 3) (u : H.Dart) :
    let deg := Hypermap.nodeDegree H u fuel
    DihedralClosedFamily deg (RealHypermapHubFamily H fuel deg u) := by
  intro deg0 cd k refl hk h_in
  rcases h_in with ⟨d0, hd0, r0, rfl⟩
  have h_deg_pos : 1 ≤ deg0 := by omega
  have h_tri3 : ∀ x : H.Dart, H.face.f (H.face.f (H.face.f x)) = x :=
    fun x => face_f_three_of_faceDegree_eq_three H darts h_all h_le (h_tri x (h_all x))
  let d1 := spokeDartOriented H r0 d0 (k + 1)
  have hd1 : d1 ∈ getOrbit H.node fuel u :=
    spokeDartOriented_mem_getOrbit_of_complete H darts h_all h_le hd0 r0 (k + 1)
  cases refl with
  | false =>
    refine ⟨cartDegOriented H fuel deg0 r0 d1, ⟨d1, hd1, r0, rfl⟩, ?_⟩
    intro p hp1 hp2
    dsimp [symCartDeg, symCartPos, cartDegOriented]
    have h_sh : cartDartOriented H deg0 r0 (spokeDartOriented H r0 d0 (k + 1)) p =
        cartDartOriented H deg0 r0 d0 (shiftCartPos deg0 k p) :=
      cartDartOriented_shiftCartPos_eq H darts h_all h_le hd0 r0 hk hp1
    rw [h_sh]
  | true =>
    let d_refl := spokeDartOriented H r0 d0 deg0
    have hd_refl : d_refl ∈ getOrbit H.node fuel u :=
      spokeDartOriented_mem_getOrbit_of_complete H darts h_all h_le hd0 r0 deg0
    let d2 := spokeDartOriented H (!r0) d_refl (k + 1)
    have hd2 : d2 ∈ getOrbit H.node fuel u :=
      spokeDartOriented_mem_getOrbit_of_complete H darts h_all h_le hd_refl (!r0) (k + 1)
    refine ⟨cartDegOriented H fuel deg0 (!r0) d2, ⟨d2, hd2, !r0, rfl⟩, ?_⟩
    intro p hp1 hp2
    dsimp [symCartDeg, symCartPos]
    have h_sh_bnds := shiftCartPos_bounds h_deg_pos hk hp1 hp2
    have h_sh : cartDartOriented H deg0 (!r0) (spokeDartOriented H (!r0) d_refl (k + 1)) p =
        cartDartOriented H deg0 (!r0) d_refl (shiftCartPos deg0 k p) :=
      cartDartOriented_shiftCartPos_eq H darts h_all h_le hd_refl (!r0) hk hp1
    have h_sh_deg : cartDegOriented H fuel deg0 (!r0) d2 p =
        cartDegOriented H fuel deg0 (!r0) d_refl (shiftCartPos deg0 k p) := by
      dsimp [cartDegOriented, d2]
      rw [h_sh]
    rw [h_sh_deg]
    exact cartDegOriented_reflCartPos_eq H darts h_all h_le h_tri3 hd0 r0 h_deg_pos h_sh_bnds.1 h_sh_bnds.2

/-- Real-Hypermap Core Soundness of `DischargingTreesVerified` (Degrees 7–11, `ProofTree.sym` eliminated):
    on any complete triangulated hypermap `H` (`∀ d ∈ darts, Hypermap.faceDegree H d fuel = 3`),
    for any hub dart `u : H.Dart` whose vertex degree `deg = Hypermap.nodeDegree H u fuel` lies in `{7, 8, 9, 10, 11}`,
    `DischargingTreesVerified configs` guarantees that **some actual spoke dart `d0 ∈ getOrbit H.node fuel u`
    and orientation `refl : Bool`** satisfies the non-vacuous 2-way
    `CoreCartLeaf deg (getShiftedTableForDeg deg) (cartDegOriented H fuel deg refl d0)`. -/
theorem dischargingTreesVerified_hypermap_core_soundness (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_tri : ∀ d ∈ darts, Hypermap.faceDegree H d fuel = 3)
    (configs : List Configuration) (h_trees : DischargingTreesVerified configs)
    (u : H.Dart)
    (h_deg : Hypermap.nodeDegree H u fuel = 7 ∨
             Hypermap.nodeDegree H u fuel = 8 ∨
             Hypermap.nodeDegree H u fuel = 9 ∨
             Hypermap.nodeDegree H u fuel = 10 ∨
             Hypermap.nodeDegree H u fuel = 11) :
    let deg := Hypermap.nodeDegree H u fuel
    ∃ d0 ∈ getOrbit H.node fuel u, ∃ refl : Bool,
      CoreCartLeaf deg (getShiftedTableForDeg deg) (cartDegOriented H fuel deg refl d0) := by
  let deg := Hypermap.nodeDegree H u fuel
  have h_u_mem : u ∈ getOrbit H.node fuel u :=
    List.contains_iff_mem.mp (Hypermap.getOrbit_contains_self H.node fuel u)
  rcases dischargingTreesVerified_core_soundness configs h_trees deg
    (RealHypermapHubFamily H fuel deg u)
    (dihedralClosedFamily_realHypermapHubFamily H darts h_all h_le h_tri u)
    ⟨u, h_u_mem, false, rfl⟩ h_deg with ⟨cd, ⟨d0, hd0, refl, rfl⟩, h_leaf⟩
  exact ⟨d0, hd0, refl, h_leaf⟩

/-- Primal–Dual Real-Hypermap Core Soundness on `H.dual` (Degrees 7–11, `ProofTree.sym` eliminated):
    on any complete cubic primal hypermap (`∀ d ∈ darts, Hypermap.nodeDegree H d fuel = 3`, so `H.dual` is a triangulation),
    for any dual vertex (primal face) `u : H.Dart` of degree `deg ∈ {7, 8, 9, 10, 11}` in `H.dual`,
    `DischargingTreesVerified configs` guarantees that **some actual dual spoke `d0 ∈ getOrbit H.dual.node fuel u`
    and orientation `refl : Bool`** satisfies `CoreCartLeaf deg (getShiftedTableForDeg deg) (cartDegOriented H.dual fuel deg refl d0)`. -/
theorem dual_dischargingTreesVerified_hypermap_core_soundness (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel)
    (h_cubic : ∀ d ∈ darts, Hypermap.nodeDegree H d fuel = 3)
    (configs : List Configuration) (h_trees : DischargingTreesVerified configs)
    (u : H.Dart)
    (h_deg : Hypermap.nodeDegree H.dual u fuel = 7 ∨
             Hypermap.nodeDegree H.dual u fuel = 8 ∨
             Hypermap.nodeDegree H.dual u fuel = 9 ∨
             Hypermap.nodeDegree H.dual u fuel = 10 ∨
             Hypermap.nodeDegree H.dual u fuel = 11) :
    let deg := Hypermap.nodeDegree H.dual u fuel
    ∃ d0 ∈ getOrbit H.dual.node fuel u, ∃ refl : Bool,
      CoreCartLeaf deg (getShiftedTableForDeg deg) (cartDegOriented H.dual fuel deg refl d0) := by
  have h_tri_dual : ∀ d ∈ darts, Hypermap.faceDegree H.dual d fuel = 3 := by
    intro d hd
    have h_closes := Hypermap.orbitClosesWithin_mono H.node d d
      (Hypermap.orbitClosesWithin_of_complete H.node darts h_all d) h_le
    dsimp [Hypermap.faceDegree, Hypermap.dual]
    rw [Hypermap.getOrbit_symm_length_eq H.node fuel d h_closes]
    exact h_cubic d hd
  exact dischargingTreesVerified_hypermap_core_soundness H.dual darts h_all h_le h_tri_dual configs h_trees u h_deg

/-- Mapping `fun i => Hypermap.Perm.iter p (i - 1) d0` over `List.range' a n` (`1 ≤ a`)
    equals `Hypermap.iterList p (Hypermap.Perm.iter p (a - 1) d0) n`. -/
theorem map_range'_perm_iter_eq_iterList {D : Type} (p : Perm D) (d0 : D) :
    ∀ (n a : Nat), 1 ≤ a →
      (List.range' a n).map (fun i => Hypermap.Perm.iter p (i - 1) d0) =
        Hypermap.iterList p (Hypermap.Perm.iter p (a - 1) d0) n
  | 0, _, _ => rfl
  | n + 1, a, ha => by
    dsimp [List.range', Hypermap.iterList]
    rw [map_range'_perm_iter_eq_iterList p d0 n (a + 1) (by omega)]
    have h_step : Hypermap.Perm.iter p (a + 1 - 1) d0 = p.f (Hypermap.Perm.iter p (a - 1) d0) := by
      have h_eq : a + 1 - 1 = (a - 1) + 1 := by omega
      rw [h_eq, Hypermap.Perm.iter_succ]
    rw [h_step]

/-- Mapping `spokeDartOriented H refl d0` over `List.range' 1 deg` equals
    `Hypermap.iterList (nodePermOriented H refl) d0 deg`. -/
theorem map_range'_spokeDartOriented_eq_iterList (H : Hypermap) (refl : Bool) (d0 : H.Dart) (deg : Nat) :
    (List.range' 1 deg).map (spokeDartOriented H refl d0) =
      Hypermap.iterList (nodePermOriented H refl) d0 deg := by
  have h_fn : spokeDartOriented H refl d0 = fun i => Hypermap.Perm.iter (nodePermOriented H refl) (i - 1) d0 := by
    funext i
    exact spokeDartOriented_eq_iter H refl d0 i
  rw [h_fn]
  simpa using map_range'_perm_iter_eq_iterList (nodePermOriented H refl) d0 deg 1 (Nat.le_refl 1)

theorem foldl_add_reverse {α : Type} (l : List α) (f : α → Int) :
    l.reverse.foldl (fun acc x => acc + f x) 0 =
      l.foldl (fun acc x => acc + f x) 0 := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    rw [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
        foldl_add_cons, ih]
    omega

/-- Spoke-Sum Decomposition of `orbitNetShift`:
    for any dart `d0 ∈ getOrbit H.node fuel u` and orientation `refl : Bool` on a complete dart list,
    `orbitNetShift H fuel u` equals the sum of `netDartShift H fuel (spokeDartOriented H refl d0 i)`
    over `i ∈ List.range' 1 (Hypermap.nodeDegree H u fuel)`. -/
theorem orbitNetShift_eq_spokeDartOriented_foldl (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ x : H.Dart, x ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) {u d0 : H.Dart}
    (hd0 : d0 ∈ getOrbit H.node fuel u) (refl : Bool) :
    let deg := Hypermap.nodeDegree H u fuel
    orbitNetShift H fuel u =
      (List.range' 1 deg).foldl (fun acc i => acc + netDartShift H fuel (spokeDartOriented H refl d0 i)) 0 := by
  intro deg0
  dsimp [orbitNetShift]
  rw [← foldl_add_map (List.range' 1 deg0) (spokeDartOriented H refl d0) (netDartShift H fuel),
      map_range'_spokeDartOriented_eq_iterList]
  have h_closes_u := Hypermap.orbitClosesWithin_mono H.node u u
    (Hypermap.orbitClosesWithin_of_complete H.node darts h_all u) h_le
  have h_closes_d0 := Hypermap.orbitClosesWithin_mono H.node d0 d0
    (Hypermap.orbitClosesWithin_of_complete H.node darts h_all d0) h_le
  have h_len_d0 : (getOrbit H.node fuel d0).length = deg0 :=
    Hypermap.getOrbit_length_eq_of_mem H.node fuel h_closes_u hd0
  have h_len_oriented : (getOrbit (nodePermOriented H refl) fuel d0).length = deg0 := by
    cases refl with
    | false => exact h_len_d0
    | true =>
      dsimp [nodePermOriented]
      rw [Hypermap.getOrbit_symm_length_eq H.node fuel d0 h_closes_d0]
      exact h_len_d0
  have h_rev := Hypermap.getOrbit_eq_reverse_iterList_of_complete (nodePermOriented H refl) darts h_all h_le d0
  rw [h_len_oriented] at h_rev
  have h_iter_eq : Hypermap.iterList (nodePermOriented H refl) d0 deg0 =
      (getOrbit (nodePermOriented H refl) fuel d0).reverse := by
    rw [h_rev, List.reverse_reverse]
  rw [h_iter_eq, foldl_add_reverse]
  have h_nodup_u : (getOrbit H.node fuel u).Nodup := Hypermap.getOrbit_nodup H.node fuel u
  have h_nodup_or : (getOrbit (nodePermOriented H refl) fuel d0).Nodup :=
    Hypermap.getOrbit_nodup (nodePermOriented H refl) fuel d0
  apply nodup_foldl_add_eq_of_iff_mem (netDartShift H fuel) h_nodup_u h_nodup_or
  intro x
  have h_iff_d0 : x ∈ getOrbit H.node fuel u ↔ x ∈ getOrbit H.node fuel d0 :=
    (Hypermap.mem_getOrbit_iff_of_mem H.node fuel h_closes_u hd0 x).symm
  rw [h_iff_d0]
  cases refl with
  | false => exact Iff.rfl
  | true =>
    dsimp [nodePermOriented]
    exact (Hypermap.mem_getOrbit_symm_perm_iff H.node fuel d0 x h_closes_d0).symm

/-!
### Stage N.3: Declarative Rule-to-`FastPosOut` Compilation & SWAR Elimination (`compiledOutletsForSpoke`, `activeOutletSum_eq_compiledOutletsSum`)
-/

/-- Computable validity check for an RSST degree bound `bnd = (low, upp)`:
    after normalizing `upp = 9 ↦ 12` and `low = 0 ↦ upp`, `5 ≤ low ≤ 9` and (`upp ≤ 8` or `upp = 12`). -/
def validRSSTBound (bnd : Nat × Nat) : Bool :=
  let upp := if bnd.2 == 9 then 12 else bnd.2
  let low := if bnd.1 == 0 then upp else bnd.1
  decide (5 ≤ low) && decide (low ≤ 9) && (decide (upp ≤ 8) || decide (upp == 12))

/-- 5-bit forbidden degree mask (`0..31`) associated with an RSST bound `bnd = (low, upp)`:
    bit `0..4` is set iff degree `5..9` fails `degMatchesBound`. -/
def forbidMaskOfBound (bnd : Nat × Nat) : Nat :=
  (if degMatchesBound 5 bnd then 0 else 1) |||
  (if degMatchesBound 6 bnd then 0 else 2) |||
  (if degMatchesBound 7 bnd then 0 else 4) |||
  (if degMatchesBound 8 bnd then 0 else 8) |||
  (if degMatchesBound 9 bnd then 0 else 16)

theorem testBit_forbidMaskOfBound_zero (bnd : Nat × Nat) :
    (forbidMaskOfBound bnd).testBit 0 = !degMatchesBound 5 bnd := by
  dsimp [forbidMaskOfBound]
  cases degMatchesBound 5 bnd <;> cases degMatchesBound 6 bnd <;>
    cases degMatchesBound 7 bnd <;> cases degMatchesBound 8 bnd <;>
    cases degMatchesBound 9 bnd <;> decide

theorem testBit_forbidMaskOfBound_one (bnd : Nat × Nat) :
    (forbidMaskOfBound bnd).testBit 1 = !degMatchesBound 6 bnd := by
  dsimp [forbidMaskOfBound]
  cases degMatchesBound 5 bnd <;> cases degMatchesBound 6 bnd <;>
    cases degMatchesBound 7 bnd <;> cases degMatchesBound 8 bnd <;>
    cases degMatchesBound 9 bnd <;> decide

theorem testBit_forbidMaskOfBound_two (bnd : Nat × Nat) :
    (forbidMaskOfBound bnd).testBit 2 = !degMatchesBound 7 bnd := by
  dsimp [forbidMaskOfBound]
  cases degMatchesBound 5 bnd <;> cases degMatchesBound 6 bnd <;>
    cases degMatchesBound 7 bnd <;> cases degMatchesBound 8 bnd <;>
    cases degMatchesBound 9 bnd <;> decide

theorem testBit_forbidMaskOfBound_three (bnd : Nat × Nat) :
    (forbidMaskOfBound bnd).testBit 3 = !degMatchesBound 8 bnd := by
  dsimp [forbidMaskOfBound]
  cases degMatchesBound 5 bnd <;> cases degMatchesBound 6 bnd <;>
    cases degMatchesBound 7 bnd <;> cases degMatchesBound 8 bnd <;>
    cases degMatchesBound 9 bnd <;> decide

theorem testBit_forbidMaskOfBound_four (bnd : Nat × Nat) :
    (forbidMaskOfBound bnd).testBit 4 = !degMatchesBound 9 bnd := by
  dsimp [forbidMaskOfBound]
  cases degMatchesBound 5 bnd <;> cases degMatchesBound 6 bnd <;>
    cases degMatchesBound 7 bnd <;> cases degMatchesBound 8 bnd <;>
    cases degMatchesBound 9 bnd <;> decide

theorem testBit_forbidMaskOfBound_of_ge_5 (bnd : Nat × Nat) {i : Nat} (hi : 5 ≤ i) :
    (forbidMaskOfBound bnd).testBit i = false := by
  have h31 : forbidMaskOfBound bnd &&& 31 = forbidMaskOfBound bnd := by
    dsimp [forbidMaskOfBound]
    cases degMatchesBound 5 bnd <;> cases degMatchesBound 6 bnd <;>
      cases degMatchesBound 7 bnd <;> cases degMatchesBound 8 bnd <;>
      cases degMatchesBound 9 bnd <;> decide
  have h31_tb : (31 : Nat).testBit i = false := by
    have h_eq : (31 : Nat) = 2 ^ 5 - 1 := rfl
    rw [h_eq, Nat.testBit_two_pow_sub_one]
    exact decide_eq_false (by omega)
  rw [← h31, Nat.testBit_and, h31_tb, Bool.and_false]

/-- For any valid RSST bound `bnd` and any degree `d ≥ 9`, `degMatchesBound d bnd = degMatchesBound 9 bnd`. -/
theorem degMatchesBound_eq_degMatchesBound_9_of_ge_9 {bnd : Nat × Nat} {d : Nat}
    (h_val : validRSSTBound bnd = true) (hd : 9 ≤ d) :
    degMatchesBound d bnd = degMatchesBound 9 bnd := by
  dsimp [validRSSTBound, degMatchesBound] at h_val ⊢
  let upp := if bnd.2 == 9 then 12 else bnd.2
  let low := if bnd.1 == 0 then upp else bnd.1
  change (decide (5 ≤ low) && decide (low ≤ 9) && (decide (upp ≤ 8) || decide (upp == 12))) = true at h_val
  rcases Bool.and_eq_true_iff.mp h_val with ⟨h_low, h_upp⟩
  rcases Bool.and_eq_true_iff.mp h_low with ⟨_, h_low9⟩
  have h_le9 : low ≤ 9 := of_decide_eq_true h_low9
  have h_led : low ≤ d := by omega
  change (decide (low ≤ d) && (decide (upp == 12) || decide (d ≤ upp))) =
    (decide (low ≤ 9) && (decide (upp == 12) || decide (9 ≤ upp)))
  rw [decide_eq_true h_led, decide_eq_true h_le9]
  rcases Bool.or_eq_true_iff.mp h_upp with h_u8 | h_u12
  · have hu8 : upp ≤ 8 := of_decide_eq_true h_u8
    have hd_not : ¬ d ≤ upp := by omega
    have h9_not : ¬ 9 ≤ upp := by omega
    rw [decide_eq_false hd_not, decide_eq_false h9_not]
  · have hu12 : (upp == 12) = true := of_decide_eq_true h_u12
    rw [decide_eq_true hu12]
    rfl

/-- Exact equivalence between `!(forbidMaskOfBound bnd).testBit (degBitIdx d)` and `degMatchesBound d bnd`
    for all valid RSST bounds `bnd` and all vertex degrees `d ≥ 5`. -/
theorem not_testBit_forbidMaskOfBound_eq_degMatchesBound {bnd : Nat × Nat} {d : Nat}
    (h_val : validRSSTBound bnd = true) (hd : 5 ≤ d) :
    (!(forbidMaskOfBound bnd).testBit (degBitIdx d)) = degMatchesBound d bnd := by
  by_cases hd5 : d = 5
  · subst hd5
    change (!(forbidMaskOfBound bnd).testBit 0) = degMatchesBound 5 bnd
    rw [testBit_forbidMaskOfBound_zero, Bool.not_not]
  · by_cases hd6 : d = 6
    · subst hd6
      change (!(forbidMaskOfBound bnd).testBit 1) = degMatchesBound 6 bnd
      rw [testBit_forbidMaskOfBound_one, Bool.not_not]
    · by_cases hd7 : d = 7
      · subst hd7
        change (!(forbidMaskOfBound bnd).testBit 2) = degMatchesBound 7 bnd
        rw [testBit_forbidMaskOfBound_two, Bool.not_not]
      · by_cases hd8 : d = 8
        · subst hd8
          change (!(forbidMaskOfBound bnd).testBit 3) = degMatchesBound 8 bnd
          rw [testBit_forbidMaskOfBound_three, Bool.not_not]
        · have hd9 : 9 ≤ d := by omega
          have h_idx : degBitIdx d = 4 := by
            dsimp [degBitIdx]
            have hle5 : ¬ d ≤ 5 := by omega
            have h6 : (d == 6) = false := beq_false_of_ne hd6
            have h7 : (d == 7) = false := beq_false_of_ne hd7
            have h8 : (d == 8) = false := beq_false_of_ne hd8
            rw [if_neg hle5, h6, h7, h8]
            rfl
          rw [h_idx, testBit_forbidMaskOfBound_four, Bool.not_not,
              degMatchesBound_eq_degMatchesBound_9_of_ge_9 h_val hd9]

/-- Declarative 360-bit forbidden mask constructed from a list of `(pos, bnd)` conditions. -/
def forbidOfConds : List (Nat × (Nat × Nat)) → Nat
  | [] => 0
  | (p, bnd) :: rest =>
    Nat.lor (Nat.shiftLeft (forbidMaskOfBound bnd) (Nat.mul p 6)) (forbidOfConds rest)

theorem testBit_shiftLeft_forbidMaskOfBound (bnd : Nat × Nat) (q p : Nat) {i : Nat} (hi : i < 6) :
    (Nat.shiftLeft (forbidMaskOfBound bnd) (Nat.mul q 6)).testBit (p * 6 + i) =
      (if p == q then (forbidMaskOfBound bnd).testBit i else false) := by
  change ((forbidMaskOfBound bnd) <<< (q * 6)).testBit (p * 6 + i) =
    (if p == q then (forbidMaskOfBound bnd).testBit i else false)
  rw [Nat.testBit_shiftLeft]
  by_cases hpq : p = q
  · subst hpq
    have h_ge : decide (p * 6 ≤ p * 6 + i) = true := decide_eq_true (by omega)
    have h_sub : p * 6 + i - p * 6 = i := by omega
    rw [beq_self_eq_true, h_ge, h_sub]
    simp
  · have h_beq : (p == q) = false := beq_false_of_ne hpq
    rw [h_beq]
    by_cases h_ge : q * 6 ≤ p * 6 + i
    · have h_dec : decide (q * 6 ≤ p * 6 + i) = true := decide_eq_true h_ge
      have h_ge5 : 5 ≤ p * 6 + i - q * 6 := by omega
      rw [h_dec, testBit_forbidMaskOfBound_of_ge_5 bnd h_ge5]
      rfl
    · have h_dec : decide (q * 6 ≤ p * 6 + i) = false := decide_eq_false h_ge
      rw [h_dec]
      rfl

theorem list_all_and {α : Type} (l : List α) (f g : α → Bool) :
    l.all (fun x => f x && g x) = (l.all f && l.all g) := by
  induction l with
  | nil => rfl
  | cons a rest ih =>
    dsimp [List.all]
    rw [ih]
    cases f a <;> cases g a <;> cases rest.all f <;> cases rest.all g <;> rfl

theorem list_all_beq_point {l : List Nat} {q : Nat} (hq : q ∈ l) (f : Nat → Bool) :
    l.all (fun p => if p == q then f p else true) = f q := by
  cases hfq : f q with
  | true =>
    apply List.all_eq_true.mpr
    intro p _
    cases hpq : (p == q) with
    | false => rfl
    | true =>
      have h_eq : p = q := eq_of_beq hpq
      subst h_eq
      exact hfq
  | false =>
    cases h_all : l.all (fun p => if p == q then f p else true) with
    | false => rfl
    | true =>
      have h_q := List.all_eq_true.mp h_all q hq
      rw [beq_self_eq_true, hfq] at h_q
      contradiction

/-- Exact characterization of `OutletActive deg cd po` when `po.forbid = forbidOfConds conds`:
    under `∀ p ∈ 1..5*deg, 5 ≤ cd p`, `OutletActive deg cd po` equals `conds.all (fun c => degMatchesBound (cd c.1) c.2)`. -/
theorem outletActive_of_forbid_eq_forbidOfConds (deg : Nat) (cd : Nat → Nat) (po : FastPosOut)
    (conds : List (Nat × (Nat × Nat)))
    (h_forbid : po.forbid = forbidOfConds conds)
    (h_conds : ∀ c ∈ conds, 1 ≤ c.1 ∧ c.1 ≤ 5 * deg ∧ validRSSTBound c.2 = true)
    (h_min5 : ∀ p, 1 ≤ p → p ≤ 5 * deg → 5 ≤ cd p) :
    OutletActive deg cd po = conds.all (fun c => degMatchesBound (cd c.1) c.2) := by
  have h_eq_all : OutletActive deg cd po =
      (List.range' 1 (5 * deg)).all (fun p => !(forbidOfConds conds).testBit (p * 6 + degBitIdx (cd p))) := by
    dsimp [OutletActive]
    rw [h_forbid]
    congr 1
    funext p
    rw [testBit_getLaneNat (forbidOfConds conds) p (degBitIdx_lt_6 (cd p))]
  rw [h_eq_all]
  clear h_eq_all h_forbid po
  induction conds with
  | nil =>
    dsimp [forbidOfConds, List.all]
    apply List.all_eq_true.mpr
    intro p _
    rw [Nat.zero_testBit]
    rfl
  | cons c rest ih =>
    rcases c with ⟨q, bnd⟩
    have hc_head := h_conds (q, bnd) List.mem_cons_self
    rcases hc_head with ⟨hq1, hq2, h_val_bnd⟩
    have h_rest_conds : ∀ c' ∈ rest, 1 ≤ c'.1 ∧ c'.1 ≤ 5 * deg ∧ validRSSTBound c'.2 = true :=
      fun c' hc' => h_conds c' (List.mem_cons_of_mem (q, bnd) hc')
    have h_step_fn : (fun p => !(forbidOfConds ((q, bnd) :: rest)).testBit (p * 6 + degBitIdx (cd p))) =
        (fun p => (if p == q then !(forbidMaskOfBound bnd).testBit (degBitIdx (cd p)) else true) &&
          !(forbidOfConds rest).testBit (p * 6 + degBitIdx (cd p))) := by
      funext p
      have h_or : (forbidOfConds ((q, bnd) :: rest)).testBit (p * 6 + degBitIdx (cd p)) =
          ((Nat.shiftLeft (forbidMaskOfBound bnd) (Nat.mul q 6)).testBit (p * 6 + degBitIdx (cd p)) ||
            (forbidOfConds rest).testBit (p * 6 + degBitIdx (cd p))) := by
        dsimp [forbidOfConds]
        exact Nat.testBit_or _ _ _
      rw [h_or, Bool.not_or, testBit_shiftLeft_forbidMaskOfBound bnd q p (degBitIdx_lt_6 (cd p))]
      cases (p == q) <;> rfl
    rw [h_step_fn, list_all_and, ih h_rest_conds]
    have hq_mem : q ∈ List.range' 1 (5 * deg) :=
      List.mem_range'.mpr ⟨q - 1, by omega, by omega⟩
    rw [list_all_beq_point hq_mem]
    have h_m := not_testBit_forbidMaskOfBound_eq_degMatchesBound h_val_bnd (h_min5 q hq1 hq2)
    dsimp [List.all]
    rw [h_m]

/-- Computable counterpart to `lookupListRec`. -/
def lookupListPure {a : Type} (d : a) : List a → Nat → a
  | [], _ => d
  | x :: _, 0 => x
  | _ :: xs, n + 1 => lookupListPure d xs n

theorem lookupListRec_eq_pure {a : Type} (d : a) (l : List a) (idx : Nat) :
    lookupListRec d l idx = lookupListPure d l idx := by
  induction l generalizing idx with
  | nil => rfl
  | cons x xs ih =>
    cases idx with
    | zero => rfl
    | succ n => exact ih n

/-- Pure pattern-matching lookup for `U[z]` (`z ∈ 0..16`) from `Rules.lean`. -/
def ruleU : Nat → Nat
  | 3 | 7 => 1
  | 5 | 9 | 11 => 3
  | 6 => 2
  | 8 => 4
  | 10 => 8
  | 14 => 5
  | 15 => 6
  | 16 => 15
  | _ => 0

/-- Pure pattern-matching lookup for `V[z]` (`z ∈ 0..16`) from `Rules.lean`. -/
def ruleV : Nat → Nat
  | 2 | 6 | 15 | 16 => 1
  | 4 | 8 | 10 => 2
  | 7 => 3
  | 9 => 5
  | 11 => 9
  | 12 => 4
  | 13 => 12
  | _ => 0

/-- Pure triangle third-vertex lookup (`63` if `(u, v)` is not a directed edge of `(x, y, z)`). -/
def pureTriAdj (x y z u v : Nat) : Nat :=
  if u == x && v == y then z
  else if u == y && v == z then x
  else if u == z && v == x then y
  else 63

/-- Pure spoke-sector triangle lookup around spoke `i ∈ 1..deg` with fan degree `k` (`0` or `5..8`). -/
def pureSpokeAdj (deg i k u v : Nat) : Nat :=
  let h := if i == 1 then deg else i - 1
  let a := deg + h
  let b := deg + i
  let c := 2 * deg + i
  let d := 3 * deg + i
  let e := 4 * deg + i
  let r1 := pureTriAdj 0 h i u v
  if r1 != 63 then r1
  else
    let r2 := pureTriAdj i h a u v
    if r2 != 63 then r2
    else if k == 5 then pureTriAdj i a b u v
    else if k == 6 then
      let r3 := pureTriAdj i a c u v
      if r3 != 63 then r3 else pureTriAdj i c b u v
    else if k == 7 then
      let r3 := pureTriAdj i a c u v
      if r3 != 63 then r3
      else
        let r4 := pureTriAdj i c d u v
        if r4 != 63 then r4 else pureTriAdj i d b u v
    else if k == 8 then
      let r3 := pureTriAdj i a c u v
      if r3 != 63 then r3
      else
        let r4 := pureTriAdj i c d u v
        if r4 != 63 then r4
        else
          let r5 := pureTriAdj i d e u v
          if r5 != 63 then r5 else pureTriAdj i e b u v
    else 63

/-- Look up the exact degree (`0` if not fixed) of spoke `i` in `fanDeg`. -/
def lookupFanDeg (i : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | (p, d) :: rest => if p == i then d else lookupFanDeg i rest

/-- Pure cartwheel adjacency lookup across all spokes `i ∈ 1..deg`. -/
def pureCartAdj (deg : Nat) (fanDeg : List (Nat × Nat)) (u v : Nat) : Nat :=
  (List.range' 1 deg).foldl (fun acc i =>
    if acc != 63 then acc
    else pureSpokeAdj deg i (lookupFanDeg i fanDeg) u v) 63

/-- Look up the cartwheel position of rule vertex `z` in `phi`. -/
def lookupPhi (z : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | (k, v) :: rest => if k == z then v else lookupPhi z rest

/-- Normalize an RSST bound `(low1, upp1)` by mapping `upp1 = 9 ↦ 12` and `low1 = 0 ↦ upp1`. -/
def normRSSTBound (bnd : Nat × Nat) : Nat × Nat :=
  let upp := if bnd.2 == 9 then 12 else bnd.2
  let low := if bnd.1 == 0 then upp else bnd.1
  (low, upp)

/-- Pure compilation of `r.triples` into shifted cartwheel `(pos, (low, upp))` conditions at spoke `x`. -/
def compileRuleTriples (deg x : Nat) (inv : Bool) :
    List (Nat × (Nat × Nat)) → List (Nat × Nat) → List (Nat × Nat) → List (Nat × (Nat × Nat))
  | [], _, _ => []
  | (z, bnd) :: rest, phi, fanDeg =>
    let nb := normRSSTBound bnd
    let u := lookupPhi (if inv then ruleV z else ruleU z) phi
    let v := lookupPhi (if inv then ruleU z else ruleV z) phi
    let pos_i := pureCartAdj deg fanDeg u v
    let phi' := (z, pos_i) :: phi
    let fanDeg' := if pos_i ≤ deg && nb.1 == nb.2 then (pos_i, nb.1) :: fanDeg else fanDeg
    (shiftCartPos deg (x - 1) pos_i, nb) :: compileRuleTriples deg x inv rest phi' fanDeg'

/-- Pure compilation of a single oriented RSST `RawRule` (`isPos`: inflow `+1` vs outflow `-1`;
    `inv`: unreflected `false` vs reflected `true`) at hub degree `deg` and spoke `x`. -/
def compileRuleOutlet (deg x : Nat) (isPos inv : Bool) (r : RawRule) :
    Option (Bool × List (Nat × (Nat × Nat))) :=
  let bHub := normRSSTBound (if isPos then r.b1 else r.b0)
  let bSpk := normRSSTBound (if isPos then r.b0 else r.b1)
  if decide (bHub.1 ≤ deg) && decide (deg ≤ bHub.2) then
    let phi0 := if isPos then [(0, 1), (1, 0)] else [(0, 0), (1, 1)]
    let fan0 := if bSpk.1 == bSpk.2 then [(1, bSpk.1)] else []
    let headCond := (shiftCartPos deg (x - 1) 1, bSpk)
    some (isPos, headCond :: compileRuleTriples deg x inv r.triples phi0 fan0)
  else
    none

/-- Pure compilation of all outlets generated by a single `r : RawRule` at hub degree `deg` and spoke `x`. -/
def compileRuleAllOutlets (deg x : Nat) (r : RawRule) : List (Bool × List (Nat × (Nat × Nat))) :=
  (match compileRuleOutlet deg x true false r with | some o => [o] | none => []) ++
  (match compileRuleOutlet deg x false false r with | some o => [o] | none => []) ++
  (if r.invert then
    (match compileRuleOutlet deg x true true r with | some o => [o] | none => []) ++
    (match compileRuleOutlet deg x false true r with | some o => [o] | none => [])
   else [])

/-- Declarative list of `(isPos, conds)` pairs compiled directly from `theRules` at spoke `x`. -/
def compiledOutletsForSpoke (deg x : Nat) : List (Bool × List (Nat × (Nat × Nat))) :=
  theRules.foldr (fun r acc => compileRuleAllOutlets deg x r ++ acc) []

/-- Declarative activation predicate for a compiled outlet `co = (isPos, conds)` on `cd`. -/
def compiledOutletActive (cd : Nat → Nat) (co : Bool × List (Nat × (Nat × Nat))) : Bool :=
  co.2.all (fun c => degMatchesBound (cd c.1) c.2)

/-- Declarative sum of signed outlet values (`+1` or `-1`) over a list of compiled outlets. -/
def compiledOutletsSum (cd : Nat → Nat) : List (Bool × List (Nat × (Nat × Nat))) → Int
  | [] => 0
  | co :: rest =>
    (if compiledOutletActive cd co then (if co.1 then 1 else -1) else 0) +
      compiledOutletsSum cd rest

/-- Computable validity check for a condition list `conds` at hub degree `deg`. -/
def validCondList (deg : Nat) (conds : List (Nat × (Nat × Nat))) : Bool :=
  conds.all (fun c => decide (1 ≤ c.1) && decide (c.1 ≤ 5 * deg) && validRSSTBound c.2)

/-- Computable structural equivalence check between a SWAR `List FastPosOut` and a declarative
    `List (Bool × List (Nat × (Nat × Nat)))` at hub degree `deg`. -/
def matchesCompiledOutlets (deg : Nat) : List FastPosOut → List (Bool × List (Nat × (Nat × Nat))) → Bool
  | [], [] => true
  | po :: pos, co :: cos =>
    (po.isPos == co.1) &&
    (po.forbid == forbidOfConds co.2) &&
    validCondList deg co.2 &&
    matchesCompiledOutlets deg pos cos
  | _, _ => false

/-- Computable verification that every spoke `x ∈ 1..deg` in `getShiftedTableForDeg deg`
    matches `compiledOutletsForSpoke deg x`. -/
def validCompiledShiftedTable (deg : Nat) : Bool :=
  (List.range' 1 deg).all (fun x =>
    matchesCompiledOutlets deg
      (lookupListPure [] (getShiftedTableForDeg deg) x)
      (compiledOutletsForSpoke deg x))

set_option maxRecDepth 200000 in
theorem validCompiledShiftedTable_7 : validCompiledShiftedTable 7 = true := by decide

set_option maxRecDepth 200000 in
theorem validCompiledShiftedTable_8 : validCompiledShiftedTable 8 = true := by decide

set_option maxRecDepth 200000 in
theorem validCompiledShiftedTable_9 : validCompiledShiftedTable 9 = true := by decide

set_option maxRecDepth 200000 in
theorem validCompiledShiftedTable_10 : validCompiledShiftedTable 10 = true := by decide

set_option maxRecDepth 200000 in
theorem validCompiledShiftedTable_11 : validCompiledShiftedTable 11 = true := by decide

theorem validCompiledShiftedTable_getShiftedTableForDeg (deg : Nat)
    (h_deg : deg = 7 ∨ deg = 8 ∨ deg = 9 ∨ deg = 10 ∨ deg = 11) :
    validCompiledShiftedTable deg = true := by
  rcases h_deg with rfl | rfl | rfl | rfl | rfl
  · exact validCompiledShiftedTable_7
  · exact validCompiledShiftedTable_8
  · exact validCompiledShiftedTable_9
  · exact validCompiledShiftedTable_10
  · exact validCompiledShiftedTable_11

theorem validCondList_sound (deg : Nat) (conds : List (Nat × (Nat × Nat)))
    (h_val : validCondList deg conds = true) :
    ∀ c ∈ conds, 1 ≤ c.1 ∧ c.1 ≤ 5 * deg ∧ validRSSTBound c.2 = true := by
  intro c hc
  have h_c := List.all_eq_true.mp h_val c hc
  rcases Bool.and_eq_true_iff.mp h_c with ⟨h12, h3⟩
  rcases Bool.and_eq_true_iff.mp h12 with ⟨h1, h2⟩
  exact ⟨of_decide_eq_true h1, of_decide_eq_true h2, h3⟩

/-- Inductive soundness of `matchesCompiledOutlets`: when `matchesCompiledOutlets deg pos cos = true`
    and `∀ p ∈ 1..5*deg, 5 ≤ cd p`, `activeOutletSum deg cd pos = compiledOutletsSum cd cos`. -/
theorem activeOutletSum_eq_of_matchesCompiledOutlets (deg : Nat) (cd : Nat → Nat)
    (pos : List FastPosOut) (cos : List (Bool × List (Nat × (Nat × Nat))))
    (h_match : matchesCompiledOutlets deg pos cos = true)
    (h_min5 : ∀ p, 1 ≤ p → p ≤ 5 * deg → 5 ≤ cd p) :
    activeOutletSum deg cd pos = compiledOutletsSum cd cos := by
  induction pos generalizing cos with
  | nil =>
    cases cos with
    | nil => rfl
    | cons _ _ => contradiction
  | cons po pos ih =>
    cases cos with
    | nil => contradiction
    | cons co cos =>
      dsimp [matchesCompiledOutlets] at h_match
      rcases Bool.and_eq_true_iff.mp h_match with ⟨h123, h_rest⟩
      rcases Bool.and_eq_true_iff.mp h123 with ⟨h12, h_val_conds⟩
      rcases Bool.and_eq_true_iff.mp h12 with ⟨h_pos_eq, h_forbid_eq⟩
      have h_isPos : po.isPos = co.1 := eq_of_beq h_pos_eq
      have h_forbid : po.forbid = forbidOfConds co.2 := eq_of_beq h_forbid_eq
      have h_act : OutletActive deg cd po = compiledOutletActive cd co :=
        outletActive_of_forbid_eq_forbidOfConds deg cd po co.2 h_forbid
          (validCondList_sound deg co.2 h_val_conds) h_min5
      dsimp [activeOutletSum, compiledOutletsSum, outletVal]
      rw [h_act, h_isPos, ih cos h_rest]

/-- Exact SWAR-to-Declarative Equivalence for `activeOutletSum` (Degrees 7–11):
    for any hub degree `deg ∈ {7, 8, 9, 10, 11}`, any spoke index `1 ≤ x ≤ deg`,
    and any cartwheel degree assignment `cd` with `∀ p ∈ 1..5*deg, 5 ≤ cd p`,
    the SWAR sum `activeOutletSum deg cd (lookupListRec [] (getShiftedTableForDeg deg) x)`
    equals the declarative rule-bound sum `compiledOutletsSum cd (compiledOutletsForSpoke deg x)`. -/
theorem activeOutletSum_eq_compiledOutletsSum (deg x : Nat) (cd : Nat → Nat)
    (h_deg : deg = 7 ∨ deg = 8 ∨ deg = 9 ∨ deg = 10 ∨ deg = 11)
    (hx1 : 1 ≤ x) (hx2 : x ≤ deg)
    (h_min5 : ∀ p, 1 ≤ p → p ≤ 5 * deg → 5 ≤ cd p) :
    activeOutletSum deg cd (lookupListRec [] (getShiftedTableForDeg deg) x) =
      compiledOutletsSum cd (compiledOutletsForSpoke deg x) := by
  have h_tab := validCompiledShiftedTable_getShiftedTableForDeg deg h_deg
  have hx_mem : x ∈ List.range' 1 deg := List.mem_range'.mpr ⟨x - 1, by omega, by omega⟩
  have h_match := List.all_eq_true.mp h_tab x hx_mem
  rw [lookupListRec_eq_pure]
  exact activeOutletSum_eq_of_matchesCompiledOutlets deg cd
    (lookupListPure [] (getShiftedTableForDeg deg) x)
    (compiledOutletsForSpoke deg x) h_match h_min5

end Discharging
end Math
