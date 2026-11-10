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

/-- Exact evaluation of `ruleVertexDart H inv d 2`: steps from `(d, H.edge.f d)` in orientation `inv`. -/
theorem ruleVertexDart_two (H : Hypermap) (inv : Bool) (d : H.Dart) :
    ruleVertexDart H inv d 2 =
      if inv then H.edge.f (H.node.inv (H.edge.f (H.edge.f d)))
      else H.edge.f (H.node.f (H.edge.f d)) := by
  conv => lhs; unfold ruleVertexDart
  cases inv <;> dsimp [triStepDart, U, V] <;> simp

/-- Exact evaluation of `ruleVertexDart H inv d 3`: steps from `(H.edge.f d, d)` in orientation `inv`. -/
theorem ruleVertexDart_three (H : Hypermap) (inv : Bool) (d : H.Dart) :
    ruleVertexDart H inv d 3 =
      if inv then H.edge.f (H.node.inv (H.edge.f d))
      else H.edge.f (H.node.f d) := by
  conv => lhs; unfold ruleVertexDart
  cases inv <;> dsimp [triStepDart, U, V] <;> simp

theorem ruleVertexDart_false_two (H : Hypermap) (d : H.Dart) :
    ruleVertexDart H false d 2 = H.edge.f (H.node.f (H.edge.f d)) :=
  ruleVertexDart_two H false d

theorem ruleVertexDart_false_three (H : Hypermap) (d : H.Dart) :
    ruleVertexDart H false d 3 = H.edge.f (H.node.f d) :=
  ruleVertexDart_three H false d

theorem ruleVertexDart_true_two (H : Hypermap) (d : H.Dart) :
    ruleVertexDart H true d 2 = H.edge.f (H.node.inv (H.edge.f (H.edge.f d))) :=
  ruleVertexDart_two H true d

theorem ruleVertexDart_true_three (H : Hypermap) (d : H.Dart) :
    ruleVertexDart H true d 3 = H.edge.f (H.node.inv (H.edge.f d)) :=
  ruleVertexDart_three H true d

/-- Flanking-spoke identity (next spoke `H.node.f d`):
    in orientation `inv = false`, coordinate `2` of the incoming dart `H.edge.f d` is `H.edge.f (H.node.f d)`. -/
theorem ruleVertexDart_false_edge_two (H : Hypermap) (d : H.Dart) :
    ruleVertexDart H false (H.edge.f d) 2 = H.edge.f (H.node.f d) := by
  rw [ruleVertexDart_false_two, H.edge_involution d]

/-- Flanking-spoke identity (previous spoke `H.node.inv d`):
    in orientation `inv = true`, coordinate `3` of the incoming dart `H.edge.f d` is `H.edge.f (H.node.inv d)`. -/
theorem ruleVertexDart_true_edge_three (H : Hypermap) (d : H.Dart) :
    ruleVertexDart H true (H.edge.f d) 3 = H.edge.f (H.node.inv d) := by
  rw [ruleVertexDart_true_three, H.edge_involution d]

/-- Opposite flanking-spoke identity at coordinate `3` (`inv = false`) for incoming dart `H.edge.f d`. -/
theorem ruleVertexDart_false_edge_three (H : Hypermap) (d : H.Dart) :
    ruleVertexDart H false (H.edge.f d) 3 = H.edge.f (H.node.f (H.edge.f d)) :=
  ruleVertexDart_false_three H (H.edge.f d)

/-- Opposite flanking-spoke identity at coordinate `2` (`inv = true`) for incoming dart `H.edge.f d`. -/
theorem ruleVertexDart_true_edge_two (H : Hypermap) (d : H.Dart) :
    ruleVertexDart H true (H.edge.f d) 2 = H.edge.f (H.node.inv (H.edge.f d)) := by
  rw [ruleVertexDart_true_two, H.edge_involution d]

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
  have hf := orientOutflowDegs_le_3_of_target_deg_ge_8_of_deg2_ge_6 false
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
    (by simpa [H.edge_involution d] using h_d8)
    (by simpa [ruleVertexDart_false_edge_two] using h_next6)
  have ht := orientOutflowDegs_le_2_of_target_deg_ge_8_of_deg3_ge_6 true
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
    (by simpa [H.edge_involution d] using h_d8)
    (by simpa [ruleVertexDart_true_edge_three] using h_prev6)
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
  have hf := orientOutflowDegs_le_3_of_target_deg_ge_8_of_deg2_ge_6 false
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
    (by simpa [H.edge_involution d] using h_d8)
    (by simpa [ruleVertexDart_false_edge_two] using h_next6)
  have ht := orientOutflowDegs_le_1_of_target_deg_ge_8_of_deg3_ge_7 true
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
    (by simpa [H.edge_involution d] using h_d8)
    (by simpa [ruleVertexDart_true_edge_three] using h_prev7)
  omega

/-- Per-spoke incoming outflow bound (`≤ 3`) into a vertex `d` of degree `≥ 8`
    when the spoke's neighbor and both flanking spokes' neighbors all have degree `≥ 7`. -/
theorem dartRuleOutflow_le_3_of_deg_ge_7_of_target_deg_ge_8_of_flanking_spokes_ge_7 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_d8 : 8 ≤ Hypermap.nodeDegree H d fuel)
    (h_curr7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel)
    (h_next7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel)
    (h_prev7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel) :
    dartRuleOutflow H fuel (H.edge.f d) ≤ 3 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have hf := orientOutflowDegs_le_2_of_deg_ge_7_of_target_deg_ge_8_of_deg2_ge_7 false
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
    (by simpa using h_curr7)
    (by simpa [H.edge_involution d] using h_d8)
    (by simpa [ruleVertexDart_false_edge_two] using h_next7)
  have ht := orientOutflowDegs_le_1_of_target_deg_ge_8_of_deg3_ge_7 true
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
    (by simpa [H.edge_involution d] using h_d8)
    (by simpa [ruleVertexDart_true_edge_three] using h_prev7)
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
### Stage G.1: Higher-Coordinate `ruleVertexDart` Coincidence Invariants (`ValidRuleDegs`)
-/

/-- Single-argument step operator underlying `triStepDart H inv du dv`. -/
def nextRuleDart (H : Hypermap) (inv : Bool) (w : H.Dart) : H.Dart :=
  if inv then H.edge.f (H.node.inv (H.edge.f w))
  else H.edge.f (H.node.f w)

/-- Master recursive step equation for `ruleVertexDart`:
    in both orientations `inv = false` and `inv = true`, `ruleVertexDart H inv d (k + 2)`
    is `nextRuleDart H inv` applied to `ruleVertexDart H inv d (min (V.getD (k + 2) 0) (k + 1))`. -/
theorem ruleVertexDart_succ_succ (H : Hypermap) (inv : Bool) (d : H.Dart) (k : Nat) :
    ruleVertexDart H inv d (k + 2) =
      nextRuleDart H inv (ruleVertexDart H inv d (min (V.getD (k + 2) 0) (k + 1))) := by
  conv => lhs; unfold ruleVertexDart
  cases inv <;> rfl

/-- Coincidence class `{3, 5, 14}` (`V[3] = V[5] = 0`): `ruleVertexDart H inv d 5 = ruleVertexDart H inv d 3`. -/
theorem ruleVertexDart_five_eq_three (H : Hypermap) (inv : Bool) (d : H.Dart) :
    ruleVertexDart H inv d 5 = ruleVertexDart H inv d 3 := by
  rw [ruleVertexDart_succ_succ H inv d 3, ruleVertexDart_succ_succ H inv d 1]
  rfl

/-- Coincidence class `{3, 5, 14}` (`V[3] = V[14] = 0`): `ruleVertexDart H inv d 14 = ruleVertexDart H inv d 3`. -/
theorem ruleVertexDart_fourteen_eq_three (H : Hypermap) (inv : Bool) (d : H.Dart) :
    ruleVertexDart H inv d 14 = ruleVertexDart H inv d 3 := by
  rw [ruleVertexDart_succ_succ H inv d 12, ruleVertexDart_succ_succ H inv d 1]
  rfl

/-- Coincidence class `{2, 6, 15, 16}` (`V[2] = V[6] = 1`): `ruleVertexDart H inv d 6 = ruleVertexDart H inv d 2`. -/
theorem ruleVertexDart_six_eq_two (H : Hypermap) (inv : Bool) (d : H.Dart) :
    ruleVertexDart H inv d 6 = ruleVertexDart H inv d 2 := by
  rw [ruleVertexDart_succ_succ H inv d 4, ruleVertexDart_succ_succ H inv d 0]
  rfl

/-- Coincidence class `{2, 6, 15, 16}` (`V[2] = V[15] = 1`): `ruleVertexDart H inv d 15 = ruleVertexDart H inv d 2`. -/
theorem ruleVertexDart_fifteen_eq_two (H : Hypermap) (inv : Bool) (d : H.Dart) :
    ruleVertexDart H inv d 15 = ruleVertexDart H inv d 2 := by
  rw [ruleVertexDart_succ_succ H inv d 13, ruleVertexDart_succ_succ H inv d 0]
  rfl

/-- Coincidence class `{2, 6, 15, 16}` (`V[2] = V[16] = 1`): `ruleVertexDart H inv d 16 = ruleVertexDart H inv d 2`. -/
theorem ruleVertexDart_sixteen_eq_two (H : Hypermap) (inv : Bool) (d : H.Dart) :
    ruleVertexDart H inv d 16 = ruleVertexDart H inv d 2 := by
  rw [ruleVertexDart_succ_succ H inv d 14, ruleVertexDart_succ_succ H inv d 0]
  rfl

/-- Coincidence class `{4, 8, 10}` (`V[4] = V[8] = 2`): `ruleVertexDart H inv d 8 = ruleVertexDart H inv d 4`. -/
theorem ruleVertexDart_eight_eq_four (H : Hypermap) (inv : Bool) (d : H.Dart) :
    ruleVertexDart H inv d 8 = ruleVertexDart H inv d 4 := by
  rw [ruleVertexDart_succ_succ H inv d 6, ruleVertexDart_succ_succ H inv d 2]
  rfl

/-- Coincidence class `{4, 8, 10}` (`V[4] = V[10] = 2`): `ruleVertexDart H inv d 10 = ruleVertexDart H inv d 4`. -/
theorem ruleVertexDart_ten_eq_four (H : Hypermap) (inv : Bool) (d : H.Dart) :
    ruleVertexDart H inv d 10 = ruleVertexDart H inv d 4 := by
  rw [ruleVertexDart_succ_succ H inv d 8, ruleVertexDart_succ_succ H inv d 2]
  rfl

/-- Coincidence class `{7, 9}` (`V[7] = 3, V[9] = 5` and `ruleVertexDart 5 = ruleVertexDart 3`):
    `ruleVertexDart H inv d 9 = ruleVertexDart H inv d 7`. -/
theorem ruleVertexDart_nine_eq_seven (H : Hypermap) (inv : Bool) (d : H.Dart) :
    ruleVertexDart H inv d 9 = ruleVertexDart H inv d 7 := by
  rw [ruleVertexDart_succ_succ H inv d 7, ruleVertexDart_succ_succ H inv d 5]
  change nextRuleDart H inv (ruleVertexDart H inv d 5) = nextRuleDart H inv (ruleVertexDart H inv d 3)
  rw [ruleVertexDart_five_eq_three]

/-- Degree-profile coincidence invariant satisfied by `fun k => nodeDegree H (ruleVertexDart H inv d k) fuel`
    for every hypermap `H`, orientation `inv`, and dart `d`. -/
def ValidRuleDegs (degs : Nat → Nat) : Prop :=
  degs 5 = degs 3 ∧
  degs 14 = degs 3 ∧
  degs 6 = degs 2 ∧
  degs 15 = degs 2 ∧
  degs 16 = degs 2 ∧
  degs 8 = degs 4 ∧
  degs 10 = degs 4 ∧
  degs 9 = degs 7

/-- Every degree profile induced by `ruleVertexDart H inv d` on a hypermap `H` satisfies `ValidRuleDegs`. -/
theorem validRuleDegs_ruleVertexDart (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (inv : Bool) (d : H.Dart) :
    ValidRuleDegs (fun k => Hypermap.nodeDegree H (ruleVertexDart H inv d k) fuel) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · dsimp; rw [ruleVertexDart_five_eq_three]
  · dsimp; rw [ruleVertexDart_fourteen_eq_three]
  · dsimp; rw [ruleVertexDart_six_eq_two]
  · dsimp; rw [ruleVertexDart_fifteen_eq_two]
  · dsimp; rw [ruleVertexDart_sixteen_eq_two]
  · dsimp; rw [ruleVertexDart_eight_eq_four]
  · dsimp; rw [ruleVertexDart_ten_eq_four]
  · dsimp; rw [ruleVertexDart_nine_eq_seven]

/-- Any rule `r` that requires disjoint degree intervals `[loA, hiA]` and `[loB, hiB]` (`hiA ≤ 8`, `hiA < loB`)
    at two coordinates `kA` and `kB` with `degs kA = degs kB` cannot match `degs`. -/
theorem not_matchesRawRuleDegs_of_eq_coord (degs : Nat → Nat) (r : RawRule)
    (kA kB loA hiA loB hiB : Nat) (h_eq : degs kA = degs kB)
    (hA : (kA, (loA, hiA)) ∈ r.triples) (hB : (kB, (loB, hiB)) ∈ r.triples)
    (h_hiA : hiA ≤ 8) (h_sep : hiA < loB) :
    matchesRawRuleDegs degs r = false := by
  by_cases hk : degs kA ≤ hiA
  · exact not_matchesRawRuleDegs_of_triple_lt degs r kB loB hiB hB (by omega) (by omega)
  · exact not_matchesRawRuleDegs_of_triple_gt degs r kA loA hiA hA h_hiA (by omega)

/-!
### Stage G.2: Vanishing of Self-Conflicting Rules, Sharp `ValidRuleDegs` Outflow Bounds & Enhanced Degree-5 Flanking Bounds
-/

private def r37 : RawRule := { num := 37, b0 := (7, 7), b1 := (7, 7), triples := [(2, (6, 12)), (3, (5, 5)), (5, (6, 6)), (7, (5, 5)), (9, (5, 5)), (14, (5, 5))], invert := true }
private def r43 : RawRule := { num := 43, b0 := (7, 7), b1 := (7, 7), triples := [(2, (6, 6)), (3, (6, 12)), (4, (5, 6)), (6, (5, 5)), (12, (5, 5)), (13, (5, 5))], invert := true }
private def r45 : RawRule := { num := 45, b0 := (7, 7), b1 := (7, 7), triples := [(2, (6, 6)), (3, (6, 12)), (4, (5, 5)), (6, (5, 5)), (12, (6, 6)), (13, (5, 5))], invert := true }
private def r49 : RawRule := { num := 49, b0 := (7, 7), b1 := (7, 7), triples := [(2, (5, 5)), (3, (7, 12)), (4, (5, 5)), (5, (6, 6)), (6, (5, 5)), (12, (5, 5)), (13, (6, 6))], invert := true }
private def r53 : RawRule := { num := 53, b0 := (7, 7), b1 := (7, 7), triples := [(2, (6, 6)), (3, (7, 12)), (4, (6, 6)), (5, (5, 5)), (6, (5, 5)), (12, (6, 6)), (13, (5, 5))], invert := true }
private def r55 : RawRule := { num := 55, b0 := (7, 7), b1 := (7, 7), triples := [(2, (6, 6)), (3, (7, 7)), (4, (7, 12)), (5, (5, 6)), (6, (6, 6)), (9, (5, 5)), (15, (5, 5)), (16, (6, 12))], invert := true }
private def r66 : RawRule := { num := 66, b0 := (8, 8), b1 := (7, 7), triples := [(2, (6, 6)), (3, (7, 12)), (4, (5, 5)), (5, (6, 6)), (6, (5, 5)), (12, (5, 5)), (13, (5, 5)), (14, (5, 5))], invert := true }

/-- Under `ValidRuleDegs degs` and `degs 0 = 8`, rules `r61, r63, r64, r66` vanish identically,
    leaving only `r57` and `r59`. -/
private theorem orientOutflowDegs_eq_two_rules_of_valid_of_deg_8 (inv : Bool) (degs : Nat → Nat)
    (hV : ValidRuleDegs degs) (hb0 : degs 0 = 8) :
    orientOutflowDegs inv degs =
      (if (if inv then r57.invert else true) && matchesRawRuleDegs degs r57 then (1 : Int) else 0) +
      (if (if inv then r59.invert else true) && matchesRawRuleDegs degs r59 then (1 : Int) else 0) := by
  rw [orientOutflowDegs_eq_filter_active inv degs 8 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 8 0) = [r57, r59, r61, r63, r64, r66] := rfl
  rw [h_filt]; dsimp only [List.foldl]
  have h61 : matchesRawRuleDegs degs r61 = false :=
    not_matchesRawRuleDegs_of_eq_coord degs r61 3 5 5 5 6 6 hV.1.symm (by decide) (by decide) (by decide) (by decide)
  have h63 : matchesRawRuleDegs degs r63 = false :=
    not_matchesRawRuleDegs_of_eq_coord degs r63 3 14 5 5 6 12 hV.2.1.symm (by decide) (by decide) (by decide) (by decide)
  have h64 : matchesRawRuleDegs degs r64 = false :=
    not_matchesRawRuleDegs_of_eq_coord degs r64 3 14 5 5 6 12 hV.2.1.symm (by decide) (by decide) (by decide) (by decide)
  have h66 : matchesRawRuleDegs degs r66 = false :=
    not_matchesRawRuleDegs_of_eq_coord degs r66 5 3 6 6 7 12 hV.1 (by decide) (by decide) (by decide) (by decide)
  rw [h61, h63, h64, h66]; simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- Under `ValidRuleDegs degs` and `degs 0 = 8`, `orientOutflowDegs inv degs ≤ 2` unconditionally on `degs 1`. -/
theorem orientOutflowDegs_le_2_of_valid_of_deg_8 (inv : Bool) (degs : Nat → Nat)
    (hV : ValidRuleDegs degs) (hb0 : degs 0 = 8) :
    orientOutflowDegs inv degs ≤ 2 := by
  rw [orientOutflowDegs_eq_two_rules_of_valid_of_deg_8 inv degs hV hb0]
  have h57 : (if (if inv then r57.invert else true) && matchesRawRuleDegs degs r57 then (1 : Int) else 0) ≤ 1 := by split <;> omega
  have h59 : (if (if inv then r59.invert else true) && matchesRawRuleDegs degs r59 then (1 : Int) else 0) ≤ 1 := by split <;> omega
  omega

/-- Any dart `d` at a degree-8 vertex sends at most `4` units of rule outflow (unconditional on target degree). -/
theorem dartRuleOutflow_le_4_of_deg_8 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart) (h_d : Hypermap.nodeDegree H d fuel = 8) :
    dartRuleOutflow H fuel d ≤ 4 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have hf := orientOutflowDegs_le_2_of_valid_of_deg_8 false
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H false d k) fuel)
    (validRuleDegs_ruleVertexDart H fuel false d) (by simpa using h_d)
  have ht := orientOutflowDegs_le_2_of_valid_of_deg_8 true
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H true d k) fuel)
    (validRuleDegs_ruleVertexDart H fuel true d) (by simpa using h_d)
  omega

/-- Under `ValidRuleDegs degs`, if `8 ≤ degs 0` and `6 ≤ degs 2`, then `orientOutflowDegs inv degs = 0`. -/
theorem orientOutflowDegs_eq_zero_of_valid_of_deg_ge_8_of_deg2_ge_6 (inv : Bool) (degs : Nat → Nat)
    (hV : ValidRuleDegs degs) (hb0 : 8 ≤ degs 0) (hb2 : 6 ≤ degs 2) :
    orientOutflowDegs inv degs = 0 := by
  rcases Nat.lt_or_ge 8 (degs 0) with hgt8 | hle8
  · exact orientOutflowDegs_eq_zero_of_deg_ge_9 inv degs hgt8
  · have h8 : degs 0 = 8 := by omega
    rw [orientOutflowDegs_eq_two_rules_of_valid_of_deg_8 inv degs hV h8]
    have h57 : matchesRawRuleDegs degs r57 = false :=
      not_matchesRawRuleDegs_of_triple_gt degs r57 2 5 5 (by decide) (by decide) (by omega)
    have h59 : matchesRawRuleDegs degs r59 = false :=
      not_matchesRawRuleDegs_of_triple_gt degs r59 2 5 5 (by decide) (by decide) (by omega)
    rw [h57, h59]; simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- Under `ValidRuleDegs degs`, if `8 ≤ degs 0` and `6 ≤ degs 3`, then `orientOutflowDegs inv degs = 0`. -/
theorem orientOutflowDegs_eq_zero_of_valid_of_deg_ge_8_of_deg3_ge_6 (inv : Bool) (degs : Nat → Nat)
    (hV : ValidRuleDegs degs) (hb0 : 8 ≤ degs 0) (hb3 : 6 ≤ degs 3) :
    orientOutflowDegs inv degs = 0 := by
  rcases Nat.lt_or_ge 8 (degs 0) with hgt8 | hle8
  · exact orientOutflowDegs_eq_zero_of_deg_ge_9 inv degs hgt8
  · have h8 : degs 0 = 8 := by omega
    rw [orientOutflowDegs_eq_two_rules_of_valid_of_deg_8 inv degs hV h8]
    have h57 : matchesRawRuleDegs degs r57 = false :=
      not_matchesRawRuleDegs_of_triple_gt degs r57 3 5 5 (by decide) (by decide) (by omega)
    have h59 : matchesRawRuleDegs degs r59 = false :=
      not_matchesRawRuleDegs_of_triple_gt degs r59 3 5 5 (by decide) (by decide) (by omega)
    rw [h57, h59]; simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- Exact vanishing of incoming outflow from a neighbor `H.edge.f d` of degree `≥ 8`
    whenever both flanking spokes `H.node.f d` and `H.node.inv d` have neighbors of degree `≥ 6`. -/
theorem dartRuleOutflow_eq_zero_of_deg_ge_8_of_flanking_spokes_ge_6 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_curr8 : 8 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel)
    (h_next6 : 6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel)
    (h_prev6 : 6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel) :
    dartRuleOutflow H fuel (H.edge.f d) = 0 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have hf := orientOutflowDegs_eq_zero_of_valid_of_deg_ge_8_of_deg2_ge_6 false
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
    (validRuleDegs_ruleVertexDart H fuel false (H.edge.f d))
    (by simpa using h_curr8)
    (by simpa [ruleVertexDart_false_edge_two] using h_next6)
  have ht := orientOutflowDegs_eq_zero_of_valid_of_deg_ge_8_of_deg3_ge_6 true
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
    (validRuleDegs_ruleVertexDart H fuel true (H.edge.f d))
    (by simpa using h_curr8)
    (by simpa [ruleVertexDart_true_edge_three] using h_prev6)
  omega

/-- Under `ValidRuleDegs degs` and `degs 0 = 7`, 14 of the 21 degree-7 rules vanish identically,
    leaving only the 7 rules `[r17, r19, r21, r26, r29, r33, r41]`. -/
private theorem orientOutflowDegs_eq_seven_rules_of_valid_of_deg_7 (inv : Bool) (degs : Nat → Nat)
    (hV : ValidRuleDegs degs) (hb0 : degs 0 = 7) :
    orientOutflowDegs inv degs =
      (if (if inv then r17.invert else true) && matchesRawRuleDegs degs r17 then (1 : Int) else 0) +
      (if (if inv then r19.invert else true) && matchesRawRuleDegs degs r19 then (1 : Int) else 0) +
      (if (if inv then r21.invert else true) && matchesRawRuleDegs degs r21 then (1 : Int) else 0) +
      (if (if inv then r26.invert else true) && matchesRawRuleDegs degs r26 then (1 : Int) else 0) +
      (if (if inv then r29.invert else true) && matchesRawRuleDegs degs r29 then (1 : Int) else 0) +
      (if (if inv then r33.invert else true) && matchesRawRuleDegs degs r33 then (1 : Int) else 0) +
      (if (if inv then r41.invert else true) && matchesRawRuleDegs degs r41 then (1 : Int) else 0) := by
  rw [orientOutflowDegs_eq_filter_active inv degs 7 0 hb0 (Nat.zero_le _)]
  have h_filt : theRules.filter (ruleActiveFor 7 0) =
    [r17, r19, r21, r22, r24, r26, r27, r29, r31, r33, r35, r37, r39, r41, r43, r45, r47, r49, r51, r53, r55] := rfl
  rw [h_filt]; dsimp only [List.foldl]
  have h22 : matchesRawRuleDegs degs r22 = false :=
    not_matchesRawRuleDegs_of_eq_coord degs r22 3 5 5 5 6 12 hV.1.symm (by decide) (by decide) (by decide) (by decide)
  have h24 : matchesRawRuleDegs degs r24 = false :=
    not_matchesRawRuleDegs_of_eq_coord degs r24 3 5 5 5 6 12 hV.1.symm (by decide) (by decide) (by decide) (by decide)
  have h27 : matchesRawRuleDegs degs r27 = false :=
    not_matchesRawRuleDegs_of_eq_coord degs r27 8 4 5 5 6 6 hV.2.2.2.2.2.1 (by decide) (by decide) (by decide) (by decide)
  have h31 : matchesRawRuleDegs degs r31 = false :=
    not_matchesRawRuleDegs_of_eq_coord degs r31 3 5 5 5 7 12 hV.1.symm (by decide) (by decide) (by decide) (by decide)
  have h35 : matchesRawRuleDegs degs r35 = false :=
    not_matchesRawRuleDegs_of_eq_coord degs r35 4 8 5 5 6 6 hV.2.2.2.2.2.1.symm (by decide) (by decide) (by decide) (by decide)
  have h37 : matchesRawRuleDegs degs r37 = false :=
    not_matchesRawRuleDegs_of_eq_coord degs r37 3 5 5 5 6 6 hV.1.symm (by decide) (by decide) (by decide) (by decide)
  have h39 : matchesRawRuleDegs degs r39 = false :=
    not_matchesRawRuleDegs_of_eq_coord degs r39 3 5 5 5 6 6 hV.1.symm (by decide) (by decide) (by decide) (by decide)
  have h43 : matchesRawRuleDegs degs r43 = false :=
    not_matchesRawRuleDegs_of_eq_coord degs r43 6 2 5 5 6 6 hV.2.2.1 (by decide) (by decide) (by decide) (by decide)
  have h45 : matchesRawRuleDegs degs r45 = false :=
    not_matchesRawRuleDegs_of_eq_coord degs r45 6 2 5 5 6 6 hV.2.2.1 (by decide) (by decide) (by decide) (by decide)
  have h47 : matchesRawRuleDegs degs r47 = false :=
    not_matchesRawRuleDegs_of_eq_coord degs r47 5 3 5 5 7 7 hV.1 (by decide) (by decide) (by decide) (by decide)
  have h49 : matchesRawRuleDegs degs r49 = false :=
    not_matchesRawRuleDegs_of_eq_coord degs r49 5 3 6 6 7 12 hV.1 (by decide) (by decide) (by decide) (by decide)
  have h51 : matchesRawRuleDegs degs r51 = false :=
    not_matchesRawRuleDegs_of_eq_coord degs r51 5 3 5 5 7 7 hV.1 (by decide) (by decide) (by decide) (by decide)
  have h53 : matchesRawRuleDegs degs r53 = false :=
    not_matchesRawRuleDegs_of_eq_coord degs r53 5 3 5 5 7 12 hV.1 (by decide) (by decide) (by decide) (by decide)
  have h55 : matchesRawRuleDegs degs r55 = false :=
    not_matchesRawRuleDegs_of_eq_coord degs r55 5 3 5 6 7 7 hV.1 (by decide) (by decide) (by decide) (by decide)
  rw [h22, h24, h27, h31, h35, h37, h39, h43, h45, h47, h49, h51, h53, h55]
  simp only [Bool.and_false, if_false_eq_true_zero]; omega

/-- Under `ValidRuleDegs degs` and `degs 0 = 7`, `orientOutflowDegs false degs ≤ 4` unconditionally on `degs 1`. -/
theorem orientOutflowDegs_false_le_4_of_valid_of_deg_7 (degs : Nat → Nat)
    (hV : ValidRuleDegs degs) (hb0 : degs 0 = 7) :
    orientOutflowDegs false degs ≤ 4 := by
  rw [orientOutflowDegs_eq_seven_rules_of_valid_of_deg_7 false degs hV hb0]
  have hc17_41 := conflict_pair_at false degs r17 r41 5 5 5 6 6 (by decide) (by decide) (by decide) (by decide)
  have h19 : (if (if false then r19.invert else true) && matchesRawRuleDegs degs r19 then (1 : Int) else 0) ≤ 1 := by split <;> omega
  have h21 : (if (if false then r21.invert else true) && matchesRawRuleDegs degs r21 then (1 : Int) else 0) ≤ 1 := by split <;> omega
  have hc26_29_33 :
      (if (if false then r26.invert else true) && matchesRawRuleDegs degs r26 then (1 : Int) else 0) +
      (if (if false then r29.invert else true) && matchesRawRuleDegs degs r29 then (1 : Int) else 0) +
      (if (if false then r33.invert else true) && matchesRawRuleDegs degs r33 then (1 : Int) else 0) ≤ 1 := by
    by_cases h2 : degs 2 ≤ 5
    · have h29 : matchesRawRuleDegs degs r29 = false :=
        not_matchesRawRuleDegs_of_triple_lt degs r29 2 6 6 (by decide) (by decide) (by omega)
      have h33 : matchesRawRuleDegs degs r33 = false :=
        not_matchesRawRuleDegs_of_triple_lt degs r33 2 6 6 (by decide) (by decide) (by omega)
      have h26 : (if (if false then r26.invert else true) && matchesRawRuleDegs degs r26 then (1 : Int) else 0) ≤ 1 := by split <;> omega
      rw [h29, h33]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
    · have h26 : matchesRawRuleDegs degs r26 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r26 2 5 5 (by decide) (by decide) (by omega)
      have hc29_33 := conflict_pair_at false degs r29 r33 4 5 5 6 6 (by decide) (by decide) (by decide) (by decide)
      rw [h26]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
  omega

/-- Under `ValidRuleDegs degs` and `degs 0 = 7`, `orientOutflowDegs true degs ≤ 3` unconditionally on `degs 1`. -/
theorem orientOutflowDegs_true_le_3_of_valid_of_deg_7 (degs : Nat → Nat)
    (hV : ValidRuleDegs degs) (hb0 : degs 0 = 7) :
    orientOutflowDegs true degs ≤ 3 := by
  rw [orientOutflowDegs_eq_seven_rules_of_valid_of_deg_7 true degs hV hb0]
  have hc17_41 := conflict_pair_at true degs r17 r41 5 5 5 6 6 (by decide) (by decide) (by decide) (by decide)
  have h19 : (if (if true then r19.invert else true) && matchesRawRuleDegs degs r19 then (1 : Int) else 0) ≤ 1 := by split <;> omega
  have h21 : (if (if true then r21.invert else true) && matchesRawRuleDegs degs r21 then (1 : Int) else 0) = 0 := by
    have : r21.invert = false := rfl
    rw [this]; simp
  have h26 : (if (if true then r26.invert else true) && matchesRawRuleDegs degs r26 then (1 : Int) else 0) = 0 := by
    have : r26.invert = false := rfl
    rw [this]; simp
  have hc29_33 := conflict_pair_at true degs r29 r33 4 5 5 6 6 (by decide) (by decide) (by decide) (by decide)
  omega

/-- Any dart `d` at a degree-7 vertex sends at most `7` units of rule outflow (unconditional on target degree). -/
theorem dartRuleOutflow_le_7_of_deg_7 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart) (h_d : Hypermap.nodeDegree H d fuel = 7) :
    dartRuleOutflow H fuel d ≤ 7 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have hf := orientOutflowDegs_false_le_4_of_valid_of_deg_7
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H false d k) fuel)
    (validRuleDegs_ruleVertexDart H fuel false d) (by simpa using h_d)
  have ht := orientOutflowDegs_true_le_3_of_valid_of_deg_7
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H true d k) fuel)
    (validRuleDegs_ruleVertexDart H fuel true d) (by simpa using h_d)
  omega

/-- Universal Per-Dart Outflow Bound:
    for ANY dart `d` in ANY hypermap `H` (unconditional on both source and target degree!),
    `dartRuleOutflow H fuel d ≤ 7`. -/
theorem dartRuleOutflow_le_7 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart) :
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
      · exact dartRuleOutflow_le_7_of_deg_7 H fuel d h7
      · have := dartRuleOutflow_le_4_of_deg_8 H fuel d h8; omega

/-- Universal Per-Dart Outflow Bound for Non-Degree-7 Sources (`≤ 6`, unconditional on target degree). -/
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

/-- Under `ValidRuleDegs degs`, if `6 ≤ degs 0` and `7 ≤ degs 3`, then `orientOutflowDegs inv degs = 0`. -/
theorem orientOutflowDegs_eq_zero_of_valid_of_deg_ge_6_of_deg3_ge_7 (inv : Bool) (degs : Nat → Nat)
    (hV : ValidRuleDegs degs) (hb0 : 6 ≤ degs 0) (hb3 : 7 ≤ degs 3) :
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
    · rw [orientOutflowDegs_eq_seven_rules_of_valid_of_deg_7 inv degs hV h7]
      have h17 : matchesRawRuleDegs degs r17 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r17 3 5 6 (by decide) (by decide) (by omega)
      have h19 : matchesRawRuleDegs degs r19 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r19 3 5 6 (by decide) (by decide) (by omega)
      have h21 : matchesRawRuleDegs degs r21 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r21 3 5 5 (by decide) (by decide) (by omega)
      have h26 : matchesRawRuleDegs degs r26 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r26 3 5 5 (by decide) (by decide) (by omega)
      have h29 : matchesRawRuleDegs degs r29 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r29 3 5 5 (by decide) (by decide) (by omega)
      have h33 : matchesRawRuleDegs degs r33 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r33 3 5 5 (by decide) (by decide) (by omega)
      have h41 : matchesRawRuleDegs degs r41 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r41 3 6 6 (by decide) (by decide) (by omega)
      rw [h17, h19, h21, h26, h29, h33, h41]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
    · exact orientOutflowDegs_eq_zero_of_valid_of_deg_ge_8_of_deg3_ge_6 inv degs hV (by omega) (by omega)

/-- Under `ValidRuleDegs degs`, if `7 ≤ degs 0` and `7 ≤ degs 2`, then `orientOutflowDegs inv degs ≤ 2`. -/
theorem orientOutflowDegs_le_2_of_valid_of_deg_ge_7_of_deg2_ge_7 (inv : Bool) (degs : Nat → Nat)
    (hV : ValidRuleDegs degs) (hb0 : 7 ≤ degs 0) (hb2 : 7 ≤ degs 2) :
    orientOutflowDegs inv degs ≤ 2 := by
  rcases Nat.lt_or_ge 8 (degs 0) with hgt8 | hle8
  · have := orientOutflowDegs_eq_zero_of_deg_ge_9 inv degs hgt8; omega
  · have h_cases : degs 0 = 7 ∨ degs 0 = 8 := by omega
    rcases h_cases with h7 | h8
    · rw [orientOutflowDegs_eq_seven_rules_of_valid_of_deg_7 inv degs hV h7]
      have h21 : matchesRawRuleDegs degs r21 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r21 2 5 5 (by decide) (by decide) (by omega)
      have h26 : matchesRawRuleDegs degs r26 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r26 2 5 5 (by decide) (by decide) (by omega)
      have h29 : matchesRawRuleDegs degs r29 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r29 2 6 6 (by decide) (by decide) (by omega)
      have h33 : matchesRawRuleDegs degs r33 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r33 2 6 6 (by decide) (by decide) (by omega)
      have h41 : matchesRawRuleDegs degs r41 = false :=
        not_matchesRawRuleDegs_of_triple_gt degs r41 2 6 6 (by decide) (by decide) (by omega)
      have h17 : (if (if inv then r17.invert else true) && matchesRawRuleDegs degs r17 then (1 : Int) else 0) ≤ 1 := by split <;> omega
      have h19 : (if (if inv then r19.invert else true) && matchesRawRuleDegs degs r19 then (1 : Int) else 0) ≤ 1 := by split <;> omega
      rw [h21, h26, h29, h33, h41]; simp only [Bool.and_false, if_false_eq_true_zero]; omega
    · have := orientOutflowDegs_eq_zero_of_valid_of_deg_ge_8_of_deg2_ge_6 inv degs hV (by omega) (by omega); omega

/-- Sharp per-spoke incoming outflow bound (`≤ 2`) from any neighbor `H.edge.f d` of degree `≥ 7`
    whenever both flanking spokes `H.node.f d` and `H.node.inv d` have neighbors of degree `≥ 7`
    (unconditional on `nodeDegree H d fuel`!). -/
theorem dartRuleOutflow_le_2_of_deg_ge_7_of_flanking_spokes_ge_7 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_curr7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel)
    (h_next7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel)
    (h_prev7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel) :
    dartRuleOutflow H fuel (H.edge.f d) ≤ 2 := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have hf := orientOutflowDegs_le_2_of_valid_of_deg_ge_7_of_deg2_ge_7 false
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H false (H.edge.f d) k) fuel)
    (validRuleDegs_ruleVertexDart H fuel false (H.edge.f d))
    (by simpa using h_curr7)
    (by simpa [ruleVertexDart_false_edge_two] using h_next7)
  have ht := orientOutflowDegs_eq_zero_of_valid_of_deg_ge_6_of_deg3_ge_7 true
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H true (H.edge.f d) k) fuel)
    (validRuleDegs_ruleVertexDart H fuel true (H.edge.f d))
    (by simpa using (by omega : 6 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel))
    (by simpa [ruleVertexDart_true_edge_three] using h_prev7)
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

/-- Under `ValidRuleDegs degs`, if `degs 0 = 5`, `6 ≤ degs 1`, and `degs 3 = 5`, both `r1` and `r5` fire,
    so `2 ≤ orientOutflowDegs inv degs`. -/
theorem two_le_orientOutflowDegs_of_valid_of_deg_5_of_target_deg_ge_6_of_deg3_5 (inv : Bool) (degs : Nat → Nat)
    (hV : ValidRuleDegs degs) (hb0 : degs 0 = 5) (hb1 : 6 ≤ degs 1) (hb3 : degs 3 = 5) :
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
    rw [hb0, hV.1, hb3, decide_eq_true hb1]
    rfl
  have h_inv1 : (if inv then r1.invert else true) = true := by cases inv <;> rfl
  have h_inv5 : (if inv then r5.invert else true) = true := by cases inv <;> rfl
  have h3 : 0 ≤ (if (if inv then r3.invert else true) && matchesRawRuleDegs degs r3 then (1 : Int) else 0) := by split <;> omega
  rw [hr1, hr5, h_inv1, h_inv5]; dsimp; omega

/-- Under `ValidRuleDegs degs`, if `degs 0 = 5`, `7 ≤ degs 1`, and `degs 3 = 5`, all three rules `r1, r3, r5` fire,
    so `orientOutflowDegs inv degs = 3`. -/
theorem orientOutflowDegs_eq_3_of_valid_of_deg_5_of_target_deg_ge_7_of_deg3_5 (inv : Bool) (degs : Nat → Nat)
    (hV : ValidRuleDegs degs) (hb0 : degs 0 = 5) (hb1 : 7 ≤ degs 1) (hb3 : degs 3 = 5) :
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
    rw [hb0, hV.1, hb3, decide_eq_true (by omega : 6 ≤ degs 1)]
    rfl
  have h_inv1 : (if inv then r1.invert else true) = true := by cases inv <;> rfl
  have h_inv3 : (if inv then r3.invert else true) = true := by cases inv <;> rfl
  have h_inv5 : (if inv then r5.invert else true) = true := by cases inv <;> rfl
  rw [hr1, hr3, hr5, h_inv1, h_inv3, h_inv5]; rfl

/-- Enhanced Degree-5 Outflow Lower Bound (`≥ 3`) when `6 ≤ deg(H.edge.f d)` and the next spoke's neighbor has degree `5`. -/
theorem three_le_dartRuleOutflow_of_deg_5_of_target_deg_ge_6_of_next_spoke_5 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_d5 : Hypermap.nodeDegree H d fuel = 5)
    (h_ed6 : 6 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel)
    (h_next5 : Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel = 5) :
    3 ≤ dartRuleOutflow H fuel d := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have hf := two_le_orientOutflowDegs_of_valid_of_deg_5_of_target_deg_ge_6_of_deg3_5 false
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H false d k) fuel)
    (validRuleDegs_ruleVertexDart H fuel false d)
    (by simpa using h_d5) (by simpa using h_ed6)
    (by simpa [ruleVertexDart_false_three] using h_next5)
  have ht := one_le_orientOutflowDegs_of_deg_5_of_target_deg_ge_5 true
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H true d k) fuel)
    (by simpa using h_d5) (by simpa using (by omega : 5 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel))
  omega

/-- Enhanced Degree-5 Outflow Lower Bound (`≥ 4`) when `7 ≤ deg(H.edge.f d)` and the next spoke's neighbor has degree `5`. -/
theorem four_le_dartRuleOutflow_of_deg_5_of_target_deg_ge_7_of_next_spoke_5 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_d5 : Hypermap.nodeDegree H d fuel = 5)
    (h_ed7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel)
    (h_next5 : Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel = 5) :
    4 ≤ dartRuleOutflow H fuel d := by
  rw [dartRuleOutflow_eq_orientOutflowDegs_add]
  have hf := orientOutflowDegs_eq_3_of_valid_of_deg_5_of_target_deg_ge_7_of_deg3_5 false
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H false d k) fuel)
    (validRuleDegs_ruleVertexDart H fuel false d)
    (by simpa using h_d5) (by simpa using h_ed7)
    (by simpa [ruleVertexDart_false_three] using h_next5)
  have ht := one_le_orientOutflowDegs_of_deg_5_of_target_deg_ge_5 true
    (fun k => Hypermap.nodeDegree H (ruleVertexDart H true d k) fuel)
    (by simpa using h_d5) (by simpa using (by omega : 5 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel))
  omega

/-- Enhanced Degree-5 Net Dart Shift Upper Bound (`≤ -3`) when `6 ≤ deg(H.edge.f d)` and the next spoke's neighbor has degree `5`. -/
theorem netDartShift_le_neg_three_of_deg_5_of_target_deg_ge_6_of_next_spoke_5 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_d5 : Hypermap.nodeDegree H d fuel = 5)
    (h_ed6 : 6 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel)
    (h_next5 : Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel = 5) :
    netDartShift H fuel d ≤ -3 := by
  dsimp [netDartShift]
  have h_out := three_le_dartRuleOutflow_of_deg_5_of_target_deg_ge_6_of_next_spoke_5 H fuel d h_d5 h_ed6 h_next5
  have h_in : dartRuleOutflow H fuel (H.edge.f d) = 0 := by
    apply dartRuleOutflow_eq_zero_of_target_deg_5_of_deg_ne_5 H fuel (H.edge.f d)
    · rw [H.edge_involution d]; exact h_d5
    · omega
  omega

/-- Enhanced Degree-5 Net Dart Shift Upper Bound (`≤ -4`) when `7 ≤ deg(H.edge.f d)` and the next spoke's neighbor has degree `5`. -/
theorem netDartShift_le_neg_four_of_deg_5_of_target_deg_ge_7_of_next_spoke_5 (H : Hypermap) [DecidableEq H.Dart]
    (fuel : Nat) (d : H.Dart)
    (h_d5 : Hypermap.nodeDegree H d fuel = 5)
    (h_ed7 : 7 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel)
    (h_next5 : Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel = 5) :
    netDartShift H fuel d ≤ -4 := by
  dsimp [netDartShift]
  have h_out := four_le_dartRuleOutflow_of_deg_5_of_target_deg_ge_7_of_next_spoke_5 H fuel d h_d5 h_ed7 h_next5
  have h_in : dartRuleOutflow H fuel (H.edge.f d) = 0 := by
    apply dartRuleOutflow_eq_zero_of_target_deg_5_of_deg_ne_5 H fuel (H.edge.f d)
    · rw [H.edge_involution d]; exact h_d5
    · omega
  omega

/-!
### Stage G.3: Global Discharging Theorems for Degrees `≥ 8` (`neighbors ≥ 7`) and Degrees `≥ 6` (`neighbors ≥ 8`)
-/

/-- For any vertex `u` with `8 ≤ nodeDegree H u fuel` whose neighbors all have degree `≥ 7`,
    every spoke `d ∈ getOrbit H.node fuel u` has incoming outflow `≤ 2` and outgoing outflow `≥ 0`,
    so `netDartShift H fuel d ≤ 2` and `initialCharge H u fuel + orbitNetShift H fuel u ≤ 0`
    (since `60 - 10k + 2k = 60 - 8k ≤ -4 ≤ 0` for `k ≥ 8`). -/
theorem initialCharge_add_orbitNetShift_le_zero_of_deg_ge_8_of_neighbors_deg_ge_7 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_deg8 : 8 ≤ Hypermap.nodeDegree H u fuel)
    (h_nb7 : ∀ d ∈ getOrbit H.node fuel u, 7 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    initialCharge H u fuel + orbitNetShift H fuel u ≤ 0 := by
  dsimp [initialCharge, orbitNetShift]
  have h_le_c := foldl_add_le_of_le_const (getOrbit H.node fuel u) (fun d => netDartShift H fuel d) 2 (by
    intro d hd
    dsimp [netDartShift]
    have h_out_nonneg : 0 ≤ dartRuleOutflow H fuel d := dartRuleOutflow_nonneg H fuel d
    have hd_next : H.node.f d ∈ getOrbit H.node fuel u :=
      Hypermap.getOrbit_closed_under_f_of_complete H.node darts h_all h_le hd
    have hd_prev : H.node.inv d ∈ getOrbit H.node fuel u :=
      Hypermap.getOrbit_closed_under_inv_of_complete H.node darts h_all h_le hd
    have h_in2 : dartRuleOutflow H fuel (H.edge.f d) ≤ 2 :=
      dartRuleOutflow_le_2_of_deg_ge_7_of_flanking_spokes_ge_7 H fuel d
        (h_nb7 d hd) (h_nb7 (H.node.f d) hd_next) (h_nb7 (H.node.inv d) hd_prev)
    omega)
  dsimp at h_le_c
  have h_len : (getOrbit H.node fuel u).length = Hypermap.nodeDegree H u fuel := rfl
  omega

/-- Global Discharging Theorem for Degree `≥ 8` with Degree-`≥ 7` Neighbors:
    for any loopless vertex `u` of degree `≥ 8` whose neighbors all have degree `≥ 7`,
    `finalCharge H (rsstChargeShift H fuel) darts u ≤ 0`. -/
theorem finalCharge_le_zero_of_deg_ge_8_of_neighbors_deg_ge_7 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (h_deg8 : 8 ≤ Hypermap.nodeDegree H u fuel)
    (h_nb7 : ∀ d ∈ getOrbit H.node fuel u, 7 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    finalCharge H (rsstChargeShift H fuel) darts u ≤ 0 := by
  rw [finalCharge_eq_initialCharge_add_orbitNetShift H darts h_all h_le u h_loopless]
  exact initialCharge_add_orbitNetShift_le_zero_of_deg_ge_8_of_neighbors_deg_ge_7 H darts h_all h_le u h_deg8 h_nb7

/-- For any vertex `u` with `6 ≤ nodeDegree H u fuel` whose neighbors all have degree `≥ 8`,
    every spoke `d ∈ getOrbit H.node fuel u` has incoming outflow `= 0` and outgoing outflow `≥ 0`,
    so `netDartShift H fuel d ≤ 0` and `initialCharge H u fuel + orbitNetShift H fuel u ≤ 0`. -/
theorem initialCharge_add_orbitNetShift_le_zero_of_deg_ge_6_of_neighbors_deg_ge_8 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_deg6 : 6 ≤ Hypermap.nodeDegree H u fuel)
    (h_nb8 : ∀ d ∈ getOrbit H.node fuel u, 8 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
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
    have h_next6 : 6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.f d)) fuel := by
      have := h_nb8 (H.node.f d) hd_next; omega
    have h_prev6 : 6 ≤ Hypermap.nodeDegree H (H.edge.f (H.node.inv d)) fuel := by
      have := h_nb8 (H.node.inv d) hd_prev; omega
    have h_in0 : dartRuleOutflow H fuel (H.edge.f d) = 0 :=
      dartRuleOutflow_eq_zero_of_deg_ge_8_of_flanking_spokes_ge_6 H fuel d
        (h_nb8 d hd) h_next6 h_prev6
    omega)
  dsimp at h_le_c
  have h_len : (getOrbit H.node fuel u).length = Hypermap.nodeDegree H u fuel := rfl
  omega

/-- Global Discharging Theorem for Degree `≥ 6` (Including Degree 7!) with Degree-`≥ 8` Neighbors:
    for any loopless vertex `u` of degree `≥ 6` whose neighbors all have degree `≥ 8`,
    `finalCharge H (rsstChargeShift H fuel) darts u ≤ 0`. -/
theorem finalCharge_le_zero_of_deg_ge_6_of_neighbors_deg_ge_8 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel : Nat} (h_le : darts.length ≤ fuel) (u : H.Dart)
    (h_loopless : ∀ d ∈ getOrbit H.node fuel u, Hypermap.sameVertex H (H.edge.f d) u fuel = false)
    (h_deg6 : 6 ≤ Hypermap.nodeDegree H u fuel)
    (h_nb8 : ∀ d ∈ getOrbit H.node fuel u, 8 ≤ Hypermap.nodeDegree H (H.edge.f d) fuel) :
    finalCharge H (rsstChargeShift H fuel) darts u ≤ 0 := by
  rw [finalCharge_eq_initialCharge_add_orbitNetShift H darts h_all h_le u h_loopless]
  exact initialCharge_add_orbitNetShift_le_zero_of_deg_ge_6_of_neighbors_deg_ge_8 H darts h_all h_le u h_deg6 h_nb8

/-- Primal–Dual Discharging Theorem on `H.dual` (`deg(u) ≥ 8`, neighbors `≥ 7`):
    on any bridgeless hypermap `H`, any dual vertex `u` of degree `≥ 8` whose dual neighbors
    all have degree `≥ 7` satisfies `finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0`. -/
theorem dual_finalCharge_le_zero_of_deg_ge_8_of_isBridgeless_of_neighbors_deg_ge_7 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b fuel : Nat} (h_le_b : darts.length ≤ fuel_b) (h_le : darts.length ≤ fuel)
    (h_bridge : Hypermap.isBridgeless H darts fuel_b) (u : H.Dart)
    (h_deg8 : 8 ≤ Hypermap.nodeDegree H.dual u fuel)
    (h_nb7 : ∀ d ∈ getOrbit H.dual.node fuel u, 7 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f d) fuel) :
    finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0 := by
  have h_loopless : ∀ d ∈ getOrbit H.dual.node fuel u, Hypermap.sameVertex H.dual (H.dual.edge.f d) u fuel = false :=
    dual_loopless_orbit_of_isBridgeless H darts h_all h_le_b h_le h_bridge u
  exact finalCharge_le_zero_of_deg_ge_8_of_neighbors_deg_ge_7 H.dual darts h_all h_le u h_loopless h_deg8 h_nb7

/-- Primal–Dual Discharging Theorem on `H.dual` (`deg(u) ≥ 6`, neighbors `≥ 8`):
    on any bridgeless hypermap `H`, any dual vertex `u` of degree `≥ 6` (including degree 6 and 7)
    whose dual neighbors all have degree `≥ 8` satisfies `finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0`. -/
theorem dual_finalCharge_le_zero_of_deg_ge_6_of_isBridgeless_of_neighbors_deg_ge_8 (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_all : ∀ d : H.Dart, d ∈ darts)
    {fuel_b fuel : Nat} (h_le_b : darts.length ≤ fuel_b) (h_le : darts.length ≤ fuel)
    (h_bridge : Hypermap.isBridgeless H darts fuel_b) (u : H.Dart)
    (h_deg6 : 6 ≤ Hypermap.nodeDegree H.dual u fuel)
    (h_nb8 : ∀ d ∈ getOrbit H.dual.node fuel u, 8 ≤ Hypermap.nodeDegree H.dual (H.dual.edge.f d) fuel) :
    finalCharge H.dual (rsstChargeShift H.dual fuel) darts u ≤ 0 := by
  have h_loopless : ∀ d ∈ getOrbit H.dual.node fuel u, Hypermap.sameVertex H.dual (H.dual.edge.f d) u fuel = false :=
    dual_loopless_orbit_of_isBridgeless H darts h_all h_le_b h_le h_bridge u
  exact finalCharge_le_zero_of_deg_ge_6_of_neighbors_deg_ge_8 H.dual darts h_all h_le u h_loopless h_deg6 h_nb8

end Discharging
end Math
