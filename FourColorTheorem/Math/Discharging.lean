import FourColorTheorem.Math.HypermapGraph
import FourColorTheorem.Math.Topology.Euler
import FourColorTheorem.Math.Rules
import FourColorTheorem.Math.Coloring

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

/-- Step from a pair of reference darts `(du, dv)` in a triangulation to the third triangle vertex dart,
    oriented by `inv = false` (counterclockwise `node.f`) or `inv = true` (clockwise `node.inv`). -/
def triStepDart (H : Hypermap) (inv : Bool) (du dv : H.Dart) : H.Dart :=
  if inv then H.edge.f (H.node.inv (H.edge.f du))
  else H.edge.f (H.node.f dv)

/-- Map each RSST rule coordinate `k ∈ {0..16}` around a directed dart `d` to its vertex dart in `H`
    using the canonical RSST coordinate tables `U` and `V` from `Rules.lean`. -/
def ruleVertexDart (H : Hypermap) (inv : Bool) (d : H.Dart) : Nat → H.Dart
  | 0 => d
  | 1 => H.edge.f d
  | k + 2 =>
    let z := k + 2
    let u_idx := if inv then V.getD z 0 else U.getD z 0
    let v_idx := if inv then U.getD z 0 else V.getD z 0
    let du := ruleVertexDart H inv d (min u_idx (k + 1))
    let dv := ruleVertexDart H inv d (min v_idx (k + 1))
    triStepDart H inv du dv

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

end Discharging
end Math
