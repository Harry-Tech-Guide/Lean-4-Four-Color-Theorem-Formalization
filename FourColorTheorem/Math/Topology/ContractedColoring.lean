/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
Released under Apache 2.0 license.
-/
import FourColorTheorem.Math.Topology.DiskExcision
import FourColorTheorem.Math.Topology.ShortCircuits
import FourColorTheorem.Math.Unavoidability.FreeCompletionProjection

/-!
# Stage V.1–V.2: Contracted Coloring Existence for All 384 C-Reducible Configurations

This module eliminates `Math.RSSTStandardizationBridge` by proving that in any planar,
bridgeless minimal counterexample `H` (in primal form `H.PrimalMinimalCounterexample`), any
matched C-reducible unavoidable configuration `rc = parsedRConfList[h]` (`h < 633`) admits a
quotient 4-coloring `VertexColoringMod H.dual (mappedContractDarts p.emb)`.

1. **Certified Contract Forest & Ring-Pair Witnesses (`checkContractForestAndWitnesses`):**
   Pure-kernel `rfl` verification over `rcTable[0]!..rcTable[9]!` establishing that every
   `rc` has loopless, duplicate-free `contractEdges` with zero 3-cycles and zero 4-step
   non-backtracking walks (a simple forest of maximum path length `≤ 3`) and that every
   distinct pair `u < v < rc.r` in `V(X)` satisfies `dist1`, `dist2_int`, or `dist3_int`.
2. **Dual-Vertex Injectivity & Distinct Undirected Contract Edges (`vx_rep_distinct_in_dual`):**
   Uses `mc_no_parallel_edges_of_two_darts`, `mc_three_cycle_is_facial_dual`, and
   `MatchesConfCycle` to show all contract endpoints map to pairwise distinct `H.dual`
   vertices, and all edges of `M := mappedContractDarts p.emb` are pairwise distinct undirected
   edges in `H`.
-/

namespace Hypermap

open Math Math.Hypermap Math.Discharging Math.Unavoidability

/-! ## Section 1: Certified Contract Forest & Ring-Pair Witnesses (`rfl`) -/

section ContractForestCert

/-- Neighbor list of `u` inside a symmetric contract-edge list `ce`. -/
def ceNbrs (ce : List (Nat × Nat)) (u : Nat) : List Nat :=
  ce.filterMap fun p => if p.1 == u then some p.2 else if p.2 == u then some p.1 else none

/-- Flat list of endpoint vertices touched by `ce`. -/
def ceVerts (ce : List (Nat × Nat)) : List Nat :=
  ce.flatMap fun p => [p.1, p.2]

/-- Boolean check that `ce` has no self-loops and no duplicate unordered edges. -/
def ceNoDupUnordered : List (Nat × Nat) → Bool
  | [] => true
  | (a, b) :: rest =>
      a != b &&
      rest.all (fun q => !((q.1 == a && q.2 == b) || (q.1 == b && q.2 == a))) &&
      ceNoDupUnordered rest

/-- Boolean check that `ce` has zero 3-cycles. -/
def ceNo3Cycles (ce : List (Nat × Nat)) : Bool :=
  ce.all fun p =>
    (ceNbrs ce p.2).all fun v2 =>
      v2 == p.1 || !(isContractPair ce v2 p.1)

/-- Boolean check that `ce` has zero 4-step non-backtracking walks `(v0, v1, v2, v3, v4)`. -/
def ceNo4Walks (ce : List (Nat × Nat)) : Bool :=
  (ceVerts ce).all fun v0 =>
    (ceNbrs ce v0).all fun v1 =>
      (ceNbrs ce v1).all fun v2 =>
        v2 == v0 ||
          (ceNbrs ce v2).all fun v3 =>
            v3 == v1 ||
              (ceNbrs ce v3).all fun v4 => v4 == v2

/-- Boolean check that every distinct ring pair `u < v < rc.r` in `V(X)` is joined in `rc`
    by an edge (`dist1`), an interior wedge `w` (`dist2_int`), or an interior path `w1-w2` (`dist3_int`). -/
def ceRingPairsOK (rc : FastReducer.RConf) : Bool :=
  let ce := rc.contractEdges.toList
  let rverts := (ceVerts ce).filter (fun v => v < rc.r)
  let intCount := rc.n - rc.r
  rverts.all fun u =>
    rverts.all fun v =>
      !(u < v) ||
        symAdj rc.earlier u v ||
        ((List.range intCount).any fun k =>
          let w := rc.r + k
          symAdj rc.earlier w u && symAdj rc.earlier w v) ||
        ((List.range intCount).any fun k1 =>
          let w1 := rc.r + k1
          symAdj rc.earlier w1 u &&
            ((List.range intCount).any fun k2 =>
              let w2 := rc.r + k2
              k1 != k2 && symAdj rc.earlier w1 w2 && symAdj rc.earlier w2 v))

/-- Combined boolean certificate for Stage V.1 across `rc : RConf`. -/
def checkContractForestAndWitnesses (rc : FastReducer.RConf) : Bool :=
  let ce := rc.contractEdges.toList
  ceNoDupUnordered ce && ceNo3Cycles ce && ceNo4Walks ce && ceRingPairsOK rc

private theorem cfw_row0 : rcTable[0]!.all (fun b => b.all checkContractForestAndWitnesses) = true := rfl
private theorem cfw_row1 : rcTable[1]!.all (fun b => b.all checkContractForestAndWitnesses) = true := rfl
private theorem cfw_row2 : rcTable[2]!.all (fun b => b.all checkContractForestAndWitnesses) = true := rfl
private theorem cfw_row3 : rcTable[3]!.all (fun b => b.all checkContractForestAndWitnesses) = true := rfl
private theorem cfw_row4 : rcTable[4]!.all (fun b => b.all checkContractForestAndWitnesses) = true := rfl
private theorem cfw_row5 : rcTable[5]!.all (fun b => b.all checkContractForestAndWitnesses) = true := rfl
private theorem cfw_row6 : rcTable[6]!.all (fun b => b.all checkContractForestAndWitnesses) = true := rfl
private theorem cfw_row7 : rcTable[7]!.all (fun b => b.all checkContractForestAndWitnesses) = true := rfl
private theorem cfw_row8 : rcTable[8]!.all (fun b => b.all checkContractForestAndWitnesses) = true := rfl
private theorem cfw_row9 : rcTable[9]!.all (fun b => b.all checkContractForestAndWitnesses) = true := rfl

private theorem cfw_row_of_lt (r0 : Nat) (hr0 : r0 < 10)
    (hr0' : r0 < rcTable.length := by rw [rcTable_len]; exact hr0) :
    (rcTable[r0]'hr0').all (fun b => b.all checkContractForestAndWitnesses) = true := by
  match r0 with
  | 0 => exact cfw_row0
  | 1 => exact cfw_row1
  | 2 => exact cfw_row2
  | 3 => exact cfw_row3
  | 4 => exact cfw_row4
  | 5 => exact cfw_row5
  | 6 => exact cfw_row6
  | 7 => exact cfw_row7
  | 8 => exact cfw_row8
  | 9 => exact cfw_row9
  | _ + 10 => omega

/-- Pure-kernel certificate across all 633 RSST configurations. -/
theorem rConf_contract_forest_and_witnesses (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh) :
    checkContractForestAndWitnesses (parsedRConfList[h]'hlen) = true := by
  obtain ⟨hb0, hb1, hb2, heq⟩ := parsedRConfList_eq_table h hh
  have hrow : (rcTable[h >>> 6]'hb0).all (fun b => b.all checkContractForestAndWitnesses) = true :=
    cfw_row_of_lt (h >>> 6) (by rw [rcTable_len] at hb0; exact hb0) hb0
  have hb0_mem : rcTable[h >>> 6][((h >>> 3) &&& 7)]'hb1 ∈ rcTable[h >>> 6]'hb0 :=
    List.getElem_mem hb1
  have hcell : (rcTable[h >>> 6][((h >>> 3) &&& 7)]'hb1).all checkContractForestAndWitnesses = true :=
    (List.all_eq_true.mp hrow) _ hb0_mem
  have hb1_mem : ((rcTable[h >>> 6][((h >>> 3) &&& 7)]'hb1)[h &&& 7]'hb2) ∈
      rcTable[h >>> 6][((h >>> 3) &&& 7)]'hb1 :=
    List.getElem_mem hb2
  have hchk := (List.all_eq_true.mp hcell) _ hb1_mem
  simpa [heq] using hchk

theorem mem_ceVerts_iff {ce : List (Nat × Nat)} {u : Nat} :
    u ∈ ceVerts ce ↔ ∃ v, (u, v) ∈ ce ∨ (v, u) ∈ ce := by
  induction ce with
  | nil => simp [ceVerts]
  | cons p ps ih =>
    rcases p with ⟨a, b⟩
    simp only [ceVerts, List.flatMap_cons, List.mem_append, List.mem_cons, List.not_mem_nil,
      or_false] at ih ⊢
    constructor
    · rintro ((rfl | rfl) | hps)
      · exact ⟨b, Or.inl (Or.inl rfl)⟩
      · exact ⟨a, Or.inr (Or.inl rfl)⟩
      · obtain ⟨v, hv⟩ := ih.mp hps
        exact ⟨v, hv.elim (fun h => Or.inl (Or.inr h)) (fun h => Or.inr (Or.inr h))⟩
    · rintro ⟨v, (h1 | h1) | (h2 | h2)⟩
      · cases h1; exact Or.inl (Or.inl rfl)
      · exact Or.inr (ih.mpr ⟨v, Or.inl h1⟩)
      · cases h2; exact Or.inl (Or.inr rfl)
      · exact Or.inr (ih.mpr ⟨v, Or.inr h2⟩)

theorem mem_ceVerts_of_isContractEdge {ce : List (Nat × Nat)} {u v : Nat}
    (hce : isContractEdge ce u v = true) : u ∈ ceVerts ce ∧ v ∈ ceVerts ce := by
  have h : (u, v) ∈ ce ∨ (v, u) ∈ ce := by
    simpa [isContractEdge, Bool.or_eq_true, List.contains_iff_mem] using hce
  rcases h with huv | hvu
  · exact ⟨mem_ceVerts_iff.mpr ⟨v, Or.inl huv⟩, mem_ceVerts_iff.mpr ⟨u, Or.inr huv⟩⟩
  · exact ⟨mem_ceVerts_iff.mpr ⟨v, Or.inr hvu⟩, mem_ceVerts_iff.mpr ⟨u, Or.inl hvu⟩⟩

theorem isContractEdge_symm (ce : List (Nat × Nat)) (u v : Nat) :
    isContractEdge ce u v = isContractEdge ce v u := by
  rw [← isContractPair_eq_isContractEdge, ← isContractPair_eq_isContractEdge]
  induction ce with
  | nil => rfl
  | cons p ps ih =>
    rcases p with ⟨a, b⟩
    simp only [isContractPair, Bool.or_assoc]
    rw [ih]
    cases Nat.beq a u <;> cases Nat.beq b v <;> cases Nat.beq a v <;> cases Nat.beq b u <;> rfl

theorem ceNoDupUnordered_spec :
    ∀ {ce : List (Nat × Nat)}, ceNoDupUnordered ce = true →
      (∀ u, isContractEdge ce u u = false) ∧
      (∀ a b, (a, b) ∈ ce → (b, a) ∉ ce) ∧
      ce.Nodup
  | [], _ => ⟨fun _ => rfl, ⟨(fun _ _ h => by simp at h), List.nodup_nil⟩⟩
  | (a, b) :: rest, h => by
    simp only [ceNoDupUnordered, Bool.and_eq_true, bne_iff_ne, ne_eq, Bool.not_eq_true',
      Bool.or_eq_false_iff, Bool.and_eq_false_iff, beq_eq_false_iff_ne, List.all_eq_true] at h
    rcases h with ⟨⟨hne, hrest⟩, hrec⟩
    obtain ⟨hirr, hrev, hnd⟩ := ceNoDupUnordered_spec hrec
    refine ⟨?_, ?_, ?_⟩
    · intro u
      rw [Bool.eq_false_iff]
      intro hc
      simp only [isContractEdge, Bool.or_eq_true, List.contains_iff_mem, List.mem_cons] at hc
      rcases hc with (h1 | h1) | (h2 | h2)
      · cases h1; exact hne rfl
      · have h0 : isContractEdge rest u u = true := by simp [isContractEdge, h1]
        rw [hirr u] at h0; cases h0
      · cases h2; exact hne rfl
      · have h0 : isContractEdge rest u u = true := by simp [isContractEdge, h2]
        rw [hirr u] at h0; cases h0
    · intro x y hxy hyx
      have hx_ne : ∀ q ∈ rest, (q.1 ≠ a ∨ q.2 ≠ b) ∧ (q.1 ≠ b ∨ q.2 ≠ a) := by
        intro q hq
        have := hrest q hq
        simpa using this
      simp only [List.mem_cons] at hxy hyx
      rcases hxy with h1 | h1 <;> rcases hyx with h2 | h2
      · cases h1; cases h2; exact hne rfl
      · have := hx_ne (y, x) h2
        cases h1
        rcases this.2 with h' | h' <;> exact h' rfl
      · have := hx_ne (x, y) h1
        cases h2
        rcases this.2 with h' | h' <;> exact h' rfl
      · exact hrev x y h1 h2
    · rw [List.nodup_cons]
      refine ⟨fun hmem => ?_, hnd⟩
      have hbad := hrest (a, b) hmem
      simp at hbad

theorem mem_ceNbrs_iff {ce : List (Nat × Nat)} {u v : Nat} (hne : u ≠ v) :
    v ∈ ceNbrs ce u ↔ isContractEdge ce u v = true := by
  dsimp only [ceNbrs]
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨⟨a, b⟩, hab, hres⟩
    by_cases ha : a = u
    · subst ha
      simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hres
      subst hres
      simp [isContractEdge, hab]
    · have ha' : (a == u) = false := beq_false_of_ne ha
      by_cases hb : b = u
      · subst hb
        simp only [ha', Bool.false_eq_true, ↓reduceIte, beq_self_eq_true,
          Option.some.injEq] at hres
        subst hres
        simp [isContractEdge, hab]
      · have hb' : (b == u) = false := beq_false_of_ne hb
        simp only [ha', hb', Bool.false_eq_true, ↓reduceIte] at hres
        cases hres
  · intro hce
    simp only [isContractEdge, Bool.or_eq_true, List.contains_iff_mem] at hce
    rcases hce with huv | hvu
    · refine ⟨(u, v), huv, ?_⟩
      simp
    · refine ⟨(v, u), hvu, ?_⟩
      have hne' : (v == u) = false := beq_false_of_ne hne.symm
      simp [hne']

/-- Unpack all forest and witness guarantees for configuration `h < 633`. -/
theorem rConf_forest_props (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh) :
    let rc := parsedRConfList[h]'hlen
    let c := configOfRConf rc
    let ce := c.contractEdges
    (ceNoDupUnordered ce = true) ∧
    (∀ v0 v1 v2, isContractEdge ce v0 v1 = true → isContractEdge ce v1 v2 = true →
      v0 ≠ v1 → v1 ≠ v2 → isContractEdge ce v2 v0 = false) ∧
    (∀ v0 v1 v2 v3 v4,
      isContractEdge ce v0 v1 = true → isContractEdge ce v1 v2 = true →
      isContractEdge ce v2 v3 = true → isContractEdge ce v3 v4 = true →
      v0 ≠ v1 → v1 ≠ v2 → v2 ≠ v3 → v3 ≠ v4 →
      v2 ≠ v0 → v3 ≠ v1 → v4 ≠ v2 → False) ∧
    (∀ u v, u ∈ ceVerts ce → v ∈ ceVerts ce → u < c.ringSize → v < c.ringSize → u < v →
      c.adj u v = true ∨
      (∃ w, c.ringSize ≤ w ∧ w < c.totalNodes ∧ c.adj w u = true ∧ c.adj w v = true) ∨
      (∃ w1 w2, c.ringSize ≤ w1 ∧ w1 < c.totalNodes ∧ c.ringSize ≤ w2 ∧ w2 < c.totalNodes ∧
        w1 ≠ w2 ∧ c.adj w1 u = true ∧ c.adj w1 w2 = true ∧ c.adj w2 v = true)) := by
  intro rc c ce
  have hcfw := rConf_contract_forest_and_witnesses h hh hlen
  dsimp only [checkContractForestAndWitnesses] at hcfw
  simp only [Bool.and_eq_true] at hcfw
  rcases hcfw with ⟨⟨⟨hnd, h3⟩, h4⟩, hrw⟩
  obtain ⟨hirr, _, _⟩ := ceNoDupUnordered_spec hnd
  refine ⟨hnd, ?_, ?_, ?_⟩
  · intro v0 v1 v2 he01 he12 hne01 hne12
    rw [Bool.eq_false_iff]
    intro h20_t
    have hne20 : v2 ≠ v0 := by
      intro h_eq
      subst h_eq
      have hbad : isContractEdge ce v2 v2 = true := h20_t
      change isContractEdge rc.contractEdges.toList v2 v2 = true at hbad
      rw [hirr v2] at hbad
      cases hbad
    have h01_mem : (v0, v1) ∈ ce ∨ (v1, v0) ∈ ce := by
      simpa [isContractEdge, Bool.or_eq_true, List.contains_iff_mem] using he01
    rcases h01_mem with h01 | h10
    · have hc3 := (List.all_eq_true.mp h3) (v0, v1) h01
      have hv2_mem : v2 ∈ ceNbrs ce v1 := (mem_ceNbrs_iff hne12).mpr he12
      have hbad := (List.all_eq_true.mp hc3) v2 hv2_mem
      have hne20_b : (v2 == v0) = false := beq_false_of_ne hne20
      have hpair : isContractPair ce v2 v0 = true := (isContractPair_eq_isContractEdge ce v2 v0).symm ▸ h20_t
      change (v2 == v0 || !isContractPair ce v2 v0) = true at hbad
      rw [hne20_b, hpair] at hbad
      cases hbad
    · have hc3 := (List.all_eq_true.mp h3) (v1, v0) h10
      have he02 : isContractEdge ce v0 v2 = true := (isContractEdge_symm ce v0 v2).trans h20_t
      have hv2_mem : v2 ∈ ceNbrs ce v0 := (mem_ceNbrs_iff hne20.symm).mpr he02
      have hbad := (List.all_eq_true.mp hc3) v2 hv2_mem
      have hne21_b : (v2 == v1) = false := beq_false_of_ne hne12.symm
      have he21 : isContractEdge ce v2 v1 = true := (isContractEdge_symm ce v2 v1).trans he12
      have hpair : isContractPair ce v2 v1 = true := (isContractPair_eq_isContractEdge ce v2 v1).symm ▸ he21
      change (v2 == v1 || !isContractPair ce v2 v1) = true at hbad
      rw [hne21_b, hpair] at hbad
      cases hbad
  · intro v0 v1 v2 v3 v4 he01 he12 he23 he34 hne01 hne12 hne23 hne34 hne20 hne31 hne42
    have hv0 : v0 ∈ ceVerts ce := (mem_ceVerts_of_isContractEdge he01).1
    have hv1 : v1 ∈ ceNbrs ce v0 := (mem_ceNbrs_iff hne01).mpr he01
    have hv2 : v2 ∈ ceNbrs ce v1 := (mem_ceNbrs_iff hne12).mpr he12
    have hv3 : v3 ∈ ceNbrs ce v2 := (mem_ceNbrs_iff hne23).mpr he23
    have hv4 : v4 ∈ ceNbrs ce v3 := (mem_ceNbrs_iff hne34).mpr he34
    have h0 := (List.all_eq_true.mp h4) v0 hv0
    have h1 := (List.all_eq_true.mp h0) v1 hv1
    have h2 := (List.all_eq_true.mp h1) v2 hv2
    rw [beq_false_of_ne hne20, Bool.false_or] at h2
    have h3' := (List.all_eq_true.mp h2) v3 hv3
    rw [beq_false_of_ne hne31, Bool.false_or] at h3'
    have h4' := (List.all_eq_true.mp h3') v4 hv4
    rw [beq_false_of_ne hne42] at h4'
    cases h4'
  · intro u v hu hv hur hvr huv
    dsimp only [ceRingPairsOK] at hrw
    have hu_r : u ∈ (ceVerts ce).filter (fun x => x < rc.r) :=
      List.mem_filter.mpr ⟨hu, decide_eq_true hur⟩
    have hv_r : v ∈ (ceVerts ce).filter (fun x => x < rc.r) :=
      List.mem_filter.mpr ⟨hv, decide_eq_true hvr⟩
    have hchk := (List.all_eq_true.mp ((List.all_eq_true.mp hrw) u hu_r)) v hv_r
    have hd_uv : decide (u < v) = true := decide_eq_true huv
    simp only [Bool.or_eq_true, Bool.or_assoc, Bool.not_eq_true', hd_uv, List.any_eq_true,
      List.mem_range, Bool.and_eq_true, bne_iff_ne, ne_eq] at hchk
    have htot : c.totalNodes = rc.n := (fastConf_equiv_header h hh).2.2.2.2.1
    rcases hchk with htf | hd1 | ⟨k, hk, hd2u, hd2v⟩ | ⟨k1, hk1, h1u, k2, hk2, ⟨hne, h12⟩, h2v⟩
    · cases htf
    · exact Or.inl hd1
    · refine Or.inr (Or.inl ⟨rc.r + k, Nat.le_add_right _ _, by rw [htot]; dsimp only [rc]; omega, hd2u, hd2v⟩)
    · refine Or.inr (Or.inr ⟨rc.r + k1, rc.r + k2,
        Nat.le_add_right _ _, by rw [htot]; dsimp only [rc]; omega,
        Nat.le_add_right _ _, by rw [htot]; dsimp only [rc]; omega,
        by omega, h1u, h12, h2v⟩)

end ContractForestCert

/-! ## Section 2: Dual-Vertex Injectivity & Distinct Undirected Contract Edges -/

section DualVertexInjectivity

private theorem sameOrbit_face_of_sameVertex_dual {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts) {x y : H.Dart}
    (h : sameVertex H.dual x y darts.length = true) : SameOrbit H.face x y := by
  rw [sameVertex_iff_mem_getOrbit H.dual darts h_mc.complete (Nat.le_refl _)] at h
  have hsym := (mem_getOrbit_node_iff_mem_symm H.dual darts h_mc.complete (Nat.le_refl _) y x).mp h
  have hcl := orbitClosesWithin_of_complete H.face darts h_mc.complete y
  have hex := (mem_getOrbit_iff_exists_iter H.face darts.length y x hcl).mp hsym
  rcases hex with ⟨k, hk⟩
  exact sameOrbit_face_symm darts h_mc ⟨k, hk.symm⟩

private theorem sameVertex_dual_of_sameOrbit_face {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts) {x y : H.Dart}
    (h : SameOrbit H.face x y) : sameVertex H.dual x y darts.length = true := by
  rcases sameOrbit_face_symm darts h_mc h with ⟨k, hk⟩
  have hcl := orbitClosesWithin_of_complete H.face darts h_mc.complete y
  have hmem := (mem_getOrbit_iff_exists_iter H.face darts.length y x hcl).mpr ⟨k, hk.symm⟩
  have hsym := (mem_getOrbit_node_iff_mem_symm H.dual darts h_mc.complete (Nat.le_refl _) y x).mpr hmem
  exact (sameVertex_iff_mem_getOrbit H.dual darts h_mc.complete (Nat.le_refl _) y x).mpr hsym

private theorem dual_sameVertex_symm {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts) {x y : H.Dart}
    (h : sameVertex H.dual x y darts.length = true) :
    sameVertex H.dual y x darts.length = true := by
  rw [sameVertex_symm_of_complete H.dual darts h_mc.complete (Nat.le_refl _) y x]
  exact h

private theorem dual_sameVertex_trans {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts) {x y z : H.Dart}
    (h1 : sameVertex H.dual x y darts.length = true)
    (h2 : sameVertex H.dual y z darts.length = true) :
    sameVertex H.dual x z darts.length = true :=
  sameVertex_trans_of_complete H.dual darts h_mc.complete (Nat.le_refl _) h1 h2

private theorem mc_dual_no_self_loop {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts) (x : H.Dart) :
    sameVertex H.dual x (H.edge.f x) darts.length = false :=
  dual_sameVertex_edge_eq_false_of_isBridgeless H darts h_mc.complete (Nat.le_refl _)
    (Nat.le_refl _) h_mc.is_bridgeless x

private theorem mc_node_cube {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts) (x : H.Dart) :
    H.node.f (H.node.f (H.node.f x)) = x := by
  have hlen : (getOrbit H.node darts.length x).length = 3 :=
    mc_nodeDegree_eq_three H darts h_mc x
  have hc := perm_iter_length_getOrbit_eq_self_of_complete H.node darts h_mc.complete
    (Nat.le_refl _) x
  rw [hlen] at hc
  exact hc

private theorem mc_dual_no_parallel {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    {d1 d2 : H.Dart}
    (h1 : sameVertex H.dual d1 d2 darts.length = true)
    (h2 : sameVertex H.dual (H.edge.f d1) (H.edge.f d2) darts.length = true) :
    d1 = d2 := by
  by_cases hne : d1 = d2
  · exact hne
  · exact False.elim (mc_no_parallel_edges_of_two_darts H darts h_mc hne
      (sameOrbit_face_of_sameVertex_dual darts h_mc h1)
      (sameOrbit_face_of_sameVertex_dual darts h_mc h2))

private theorem adj_ne_vertex {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts) {u v : H.Dart}
    (hadj : areAdjacentVertices H.dual u v darts.length = true) :
    sameVertex H.dual u v darts.length = false := by
  cases h : sameVertex H.dual u v darts.length
  · rfl
  · exfalso
    have hirr := areAdjacentVertices_irrefl H.dual darts h_mc.complete (Nat.le_refl _)
      (mc_dual_no_self_loop darts h_mc) u
    have hcongr := areAdjacentVertices_congr H.dual darts h_mc.complete (Nat.le_refl _)
      (sameVertex_refl H.dual darts.length u) h
    have hadj2 : areAdjacentVertices H.dual u u darts.length = true := hcongr.trans hadj
    rw [hadj2] at hirr
    exact Bool.false_ne_true hirr.symm

private theorem faceCycleCut_disj_edge_of {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts)
    {k : Nat} (hk3 : 3 ≤ k) (rf cd : Fin k → H.Dart)
    (h_diff : ∀ i j : Fin k, i ≠ j → ¬SameOrbit H.face (rf i) (rf j))
    (h_a : ∀ i : Fin k, SameOrbit H.face (rf i) (cd i))
    (h_b : ∀ i : Fin k, SameOrbit H.face (rf ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩) (H.edge.f (cd i))) :
    ∀ i j : Fin k, H.edge.f (cd i) ≠ cd j := by
  intro i j heq
  have hbj := h_b i
  rw [heq] at hbj
  have hs1 : SameOrbit H.face (rf ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩) (rf j) :=
    sameOrbit_trans H.face hbj (sameOrbit_face_symm darts h_mc (h_a j))
  have hj_eq : j = ⟨(i.val + 1) % k, Nat.mod_lt _ (by omega)⟩ :=
    Classical.byContradiction fun hne => h_diff _ _ (fun h => hne h.symm) hs1
  have heq2 : H.edge.f (cd j) = cd i := by rw [← heq, H.edge_edge]
  have hbj2 := h_b j
  rw [heq2] at hbj2
  have hs2 : SameOrbit H.face (rf ⟨(j.val + 1) % k, Nat.mod_lt _ (by omega)⟩) (rf i) :=
    sameOrbit_trans H.face hbj2 (sameOrbit_face_symm darts h_mc (h_a i))
  have hi_eq : (⟨(j.val + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) = i :=
    Classical.byContradiction fun hne => h_diff _ _ hne hs2
  have hv := congrArg Fin.val hi_eq
  dsimp at hv
  rw [hj_eq] at hv
  dsimp at hv
  have hi_lt := i.isLt
  by_cases h1 : i.val + 1 < k
  · rw [Nat.mod_eq_of_lt h1] at hv
    by_cases h2 : i.val + 2 < k
    · rw [show i.val + 1 + 1 = i.val + 2 by omega, Nat.mod_eq_of_lt h2] at hv; omega
    · have hk2 : i.val + 1 + 1 = k := by omega
      rw [hk2, Nat.mod_self] at hv; omega
  · have hk1 : i.val + 1 = k := by omega
    rw [hk1, Nat.mod_self, Nat.zero_add, Nat.mod_eq_of_lt (by omega)] at hv; omega

private theorem sameOrbit_node_cases {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts) {x y : H.Dart}
    (h : SameOrbit H.node x y) :
    y = x ∨ y = H.node.f x ∨ H.node.f y = x := by
  rcases h with ⟨k, rfl⟩
  have hcube : ∀ z : H.Dart, H.node.f (H.node.f (H.node.f z)) = z := mc_node_cube darts h_mc
  have h3 : ∀ m : Nat, Perm.iter H.node (m + 3) x = Perm.iter H.node m x := fun m =>
    hcube (Perm.iter H.node m x)
  have h_red : ∀ q r : Nat, Perm.iter H.node (3 * q + r) x = Perm.iter H.node r x := by
    intro q
    induction q with
    | zero => intro r; simp
    | succ q ih =>
      intro r
      rw [show 3 * (q + 1) + r = (3 * q + r) + 3 by omega, h3, ih r]
  have hmod : Perm.iter H.node k x = Perm.iter H.node (k % 3) x := by
    have h1 := h_red (k / 3) (k % 3)
    rw [Nat.div_add_mod k 3] at h1
    exact h1
  rw [hmod]
  rcases (by omega : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2) with h0 | h1 | h2
  · rw [h0]; exact Or.inl rfl
  · rw [h1]; exact Or.inr (Or.inl rfl)
  · rw [h2]; exact Or.inr (Or.inr (by simpa [Perm.iter] using hcube x))

private theorem mc_three_cycle_consecutive {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts) (refl : Bool)
    {A B C d_AB d_AC : H.Dart}
    (hAB : sameVertex H.dual A B darts.length = false)
    (hBC : sameVertex H.dual B C darts.length = false)
    (hCA : sameVertex H.dual C A darts.length = false)
    (h1A : sameVertex H.dual d_AB A darts.length = true)
    (h1B : sameVertex H.dual (H.edge.f d_AB) B darts.length = true)
    (h2A : sameVertex H.dual d_AC A darts.length = true)
    (h2C : sameVertex H.dual (H.edge.f d_AC) C darts.length = true)
    (hadjBC : areAdjacentVertices H.dual B C darts.length = true) :
    (nodePermOriented H.dual refl).f d_AB = d_AC ∨
      (nodePermOriented H.dual refl).inv d_AB = d_AC := by
  have hBC_iff := (areAdjacentVertices_iff H.dual darts h_mc.complete (Nat.le_refl _) B C).mp hadjBC
  rcases hBC_iff with ⟨d_BC, hd_BCB, hd_BCC⟩
  let rf : Fin 3 → H.Dart := fun i =>
    match i.val with
    | 0 => A
    | 1 => B
    | _ => C
  let cd : Fin 3 → H.Dart := fun i =>
    match i.val with
    | 0 => d_AB
    | 1 => d_BC
    | _ => H.edge.f d_AC
  have h_diff : ∀ i j : Fin 3, i ≠ j → ¬SameOrbit H.face (rf i) (rf j) := by
    rintro ⟨iv, hiv⟩ ⟨jv, hjv⟩ hij hs
    have hsv := sameVertex_dual_of_sameOrbit_face darts h_mc hs
    rcases (by omega : iv = 0 ∨ iv = 1 ∨ iv = 2) with rfl | rfl | rfl <;>
    rcases (by omega : jv = 0 ∨ jv = 1 ∨ jv = 2) with rfl | rfl | rfl <;>
    simp only [rf] at hsv
    · exact hij rfl
    · rw [hAB] at hsv; exact Bool.false_ne_true hsv
    · rw [dual_sameVertex_symm darts h_mc hsv] at hCA; exact Bool.false_ne_true hCA.symm
    · rw [dual_sameVertex_symm darts h_mc hsv] at hAB; exact Bool.false_ne_true hAB.symm
    · exact hij rfl
    · rw [hBC] at hsv; exact Bool.false_ne_true hsv
    · rw [hCA] at hsv; exact Bool.false_ne_true hsv
    · rw [dual_sameVertex_symm darts h_mc hsv] at hBC; exact Bool.false_ne_true hBC.symm
    · exact hij rfl
  have h_a : ∀ i : Fin 3, SameOrbit H.face (rf i) (cd i) := by
    rintro ⟨iv, hiv⟩
    apply sameOrbit_face_of_sameVertex_dual darts h_mc
    rcases (by omega : iv = 0 ∨ iv = 1 ∨ iv = 2) with rfl | rfl | rfl <;> dsimp [rf, cd]
    · exact dual_sameVertex_symm darts h_mc h1A
    · exact dual_sameVertex_symm darts h_mc hd_BCB
    · exact dual_sameVertex_symm darts h_mc h2C
  have h_b : ∀ i : Fin 3, SameOrbit H.face (rf ⟨(i.val + 1) % 3, Nat.mod_lt _ (by omega)⟩) (H.edge.f (cd i)) := by
    rintro ⟨iv, hiv⟩
    apply sameOrbit_face_of_sameVertex_dual darts h_mc
    rcases (by omega : iv = 0 ∨ iv = 1 ∨ iv = 2) with rfl | rfl | rfl <;> dsimp [rf, cd]
    · exact dual_sameVertex_symm darts h_mc h1B
    · exact dual_sameVertex_symm darts h_mc hd_BCC
    · rw [H.edge_edge]; exact dual_sameVertex_symm darts h_mc h2A
  let cut : H.FaceCycleCut 3 :=
    { hk := by decide
      ringFace := rf
      cutDart := cd
      h_diff := h_diff
      h_a := h_a
      h_b := h_b
      h_disj_edge := faceCycleCut_disj_edge_of darts h_mc (by decide) rf cd h_diff h_a h_b }
  have hres : H.dual.node.f d_AB = d_AC ∨ H.dual.node.inv d_AB = d_AC := by
    rcases mc_three_cycle_is_facial_dual H darts h_mc cut with h3L | h3R
    · have horb := (mc_three_cycle_facial_orbits_dual H darts h_mc cut h3L).2.2 ⟨0, by decide⟩ ⟨2, by decide⟩
      dsimp [cut, cd] at horb
      rcases sameOrbit_node_cases darts h_mc horb with h0 | h1 | h2
      · exfalso
        have heq : H.edge.f d_AB = d_AC := by rw [← h0, H.edge_edge]
        rw [heq] at h1B
        have hAB' := dual_sameVertex_trans darts h_mc (dual_sameVertex_symm darts h_mc h2A) h1B
        rw [hAB'] at hAB; exact Bool.false_ne_true hAB.symm
      · left
        change H.face.inv d_AB = d_AC
        rw [face_inv_eq_edge_node, ← h1, H.edge_edge]
      · exfalso
        have hfnode : H.face.inv (H.edge.f d_AC) = H.edge.f d_AB := by
          rw [face_inv_eq_edge_node, h2]
        have hCB : sameVertex H.dual C B darts.length = true := by
          have hs1 : SameOrbit H.face (H.edge.f d_AC) (H.face.inv (H.edge.f d_AC)) :=
            sameOrbit_face_symm darts h_mc ⟨1, H.face.right_inv (H.edge.f d_AC)⟩
          rw [hfnode] at hs1
          have hhsv := sameVertex_dual_of_sameOrbit_face darts h_mc hs1
          exact dual_sameVertex_trans darts h_mc (dual_sameVertex_symm darts h_mc h2C)
            (dual_sameVertex_trans darts h_mc hhsv h1B)
        rw [dual_sameVertex_symm darts h_mc hCB] at hBC
        exact Bool.false_ne_true hBC.symm
    · have horb := (mc_three_cycle_facial_orbits_dual H darts h_mc cut.rev h3R).2.2 ⟨2, by decide⟩ ⟨0, by decide⟩
      have hcutR0 : cut.rev.cutDart ⟨0, by decide⟩ = H.edge.f (cd ⟨2, by decide⟩) := by
        dsimp [FaceCycleCut.rev]
      have hcutR2 : cut.rev.cutDart ⟨2, by decide⟩ = H.edge.f (cd ⟨0, by decide⟩) := by
        dsimp [FaceCycleCut.rev]
      rw [hcutR0, hcutR2] at horb
      dsimp [cd] at horb
      rw [H.edge_edge] at horb
      rcases sameOrbit_node_cases darts h_mc horb with h0 | h1 | h2
      · exfalso
        have hAB' : sameVertex H.dual A B darts.length = true := by
          rw [← h0] at h1B
          exact dual_sameVertex_trans darts h_mc (dual_sameVertex_symm darts h_mc h2A) h1B
        rw [hAB'] at hAB; exact Bool.false_ne_true hAB.symm
      · exfalso
        have hfnode : H.face.inv (H.edge.f d_AB) = H.edge.f d_AC := by
          rw [face_inv_eq_edge_node, ← h1]
        have hBC' : sameVertex H.dual B C darts.length = true := by
          have hs1 : SameOrbit H.face (H.edge.f d_AB) (H.face.inv (H.edge.f d_AB)) :=
            sameOrbit_face_symm darts h_mc ⟨1, H.face.right_inv (H.edge.f d_AB)⟩
          rw [hfnode] at hs1
          have hhsv := sameVertex_dual_of_sameOrbit_face darts h_mc hs1
          exact dual_sameVertex_trans darts h_mc (dual_sameVertex_symm darts h_mc h1B)
            (dual_sameVertex_trans darts h_mc hhsv h2C)
        rw [hBC'] at hBC; exact Bool.false_ne_true hBC.symm
      · right
        have hinv : H.face.inv d_AC = d_AB := by
          rw [face_inv_eq_edge_node, h2, H.edge_edge]
        change H.face.f d_AB = d_AC
        rw [← hinv, H.face.right_inv]
  cases refl
  · exact hres
  · simp only [nodePermOriented, Perm.symm]
    exact hres.symm

/-- Around an interior vertex `w`, consecutive darts `(p.emb.dart w a)` and `(p.emb.dart w b)`
    under `nodePermOriented H.dual p.emb.orient` force `c.adj a b = true`. -/
theorem matchesConfCycle_adj_of_step
    (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hmc : MatchesConfCycle (parsedRConfList[h]'hlen) H.dual darts p.emb)
    {w a b : Nat}
    (hwr : (configOfRConf (parsedRConfList[h]'hlen)).ringSize ≤ w)
    (hwn : w < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes)
    (han : a < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes)
    (hbn : b < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes)
    (hwa : (configOfRConf (parsedRConfList[h]'hlen)).adj w a = true)
    (hwb : (configOfRConf (parsedRConfList[h]'hlen)).adj w b = true)
    (hstep : (nodePermOriented H.dual p.emb.orient).f (p.emb.dart w a) = p.emb.dart w b) :
    (configOfRConf (parsedRConfList[h]'hlen)).adj a b = true := by
  let rc := parsedRConfList[h]'hlen
  let c := configOfRConf rc
  let fc := lookupFastConfRec h
  have hhdr := fastConf_equiv_header h hh
  have hadj := fastConf_equiv_adj h hh
  have htot : c.totalNodes = rc.n := hhdr.2.2.2.2.1
  have hadj_sz : rc.adj.size = c.totalNodes := hhdr.2.2.2.2.2.2.2.2.2.2.2.1
  have h_int_sz : fc.intVerts.length = c.interiorSize := hhdr.2.2.2.2.2.2.2.2.2.2.1
  have h_tot_eq : c.totalNodes = c.ringSize + c.interiorSize := rfl
  let iu := w - c.ringSize
  have hiu : iu < c.interiorSize := by
    change c.ringSize ≤ w at hwr
    change w < c.ringSize + c.interiorSize at hwn
    dsimp [iu]; omega
  have hiu_fc : iu < fc.intVerts.length := by rw [h_int_sz]; exact hiu
  have hu0 : c.ringSize + iu = w := by
    change c.ringSize ≤ w at hwr
    dsimp [iu]; omega
  have hiv := fastConf_equiv_intVerts h hh iu hiu
  have hwn' : w < rc.adj.size := by rw [hadj_sz]; exact hwn
  have hu0' : c.ringSize + iu < rc.adj.size := by rw [hu0]; exact hwn'
  let nbrs := (rc.adj[c.ringSize + iu]'hu0').toList
  have ha_mem : a ∈ nbrs := by
    have hc_eq := hadj.2.1 w hwn a han
    rw [hwa] at hc_eq
    have hc_mem : a ∈ (rc.adj[w]'hwn').toList := List.contains_iff_mem.mp hc_eq.symm
    simpa [nbrs, hu0] using hc_mem
  obtain ⟨j, hj, hja⟩ := List.mem_iff_getElem.mp ha_mem
  have hjc : j < fc.intVerts[iu].cyc.length := by
    have hlen_cyc : fc.intVerts[iu].cyc.length = nbrs.length := by
      simpa [nbrs, rc, fc, c] using hiv.2.2.2.2.2.2.2.1
    rw [hlen_cyc]; exact hj
  have hget := hiv.2.2.2.2.2.2.2.2.1 j hj hjc
  let cp := fc.intVerts[iu].cyc[j]'hjc
  have hcp_mem : cp ∈ fc.intVerts[iu].cyc := List.getElem_mem hjc
  have hcp_spec := hiv.2.2.2.2.2.2.2.2.2 cp hcp_mem
  let a' := if hj1 : j + 1 < nbrs.length then nbrs[j + 1]'hj1 else nbrs[0]'(by omega)
  have hcp_v : cp.v - 1 = a := by
    have hv := congrArg CycPair.v hget
    dsimp [cp] at hv
    rw [hv, Nat.add_sub_cancel]
    simpa [nbrs] using hja
  have hcp_w : cp.w - 1 = a' := by
    have hw := congrArg CycPair.w hget
    dsimp [cp] at hw
    rw [hw]
    by_cases hj1 : j + 1 < nbrs.length
    · have hj1' : j + 1 < (rc.adj[c.ringSize + iu]'hu0').size := by simpa [nbrs] using hj1
      rw [dif_pos hj1']; dsimp [a']; rw [dif_pos hj1]; simp [nbrs]; rfl
    · have hj1' : ¬ j + 1 < (rc.adj[c.ringSize + iu]'hu0').size := by simpa [nbrs] using hj1
      rw [dif_neg hj1']; dsimp [a']; rw [dif_neg hj1]; simp [nbrs]; rfl
  have ha'_lt : a' < c.totalNodes := by
    have hw1 : 1 ≤ cp.w := hcp_spec.2.2.1
    have hw2 : cp.w ≤ c.totalNodes := hcp_spec.2.2.2.1
    have hlt : cp.w - 1 < c.totalNodes := Nat.lt_of_lt_of_le (Nat.sub_lt hw1 Nat.zero_lt_one) hw2
    exact hcp_w ▸ hlt
  have hwa' : c.adj w a' = true := by
    have hw := hcp_spec.2.2.2.2.2.1
    rw [hu0, hcp_w] at hw
    exact hw
  have haa' : c.adj a a' = true := by
    have ha' := hcp_spec.2.2.2.2.2.2
    rw [hcp_v, hcp_w] at ha'
    exact ha'
  have hturn := matchesConfCycle_of_mem_cyc hh hlen hmc hiu hiu_fc hcp_mem
  change p.emb.dart (c.ringSize + iu) (cp.w - 1) =
    (nodePermOriented H.dual p.emb.orient).f (p.emb.dart (c.ringSize + iu) (cp.v - 1)) at hturn
  rw [hu0, hcp_v, hcp_w, hstep] at hturn
  have heq_ab : a' = b := by
    by_cases hne : a' = b
    · exact hne
    · exact False.elim (p.emb.int_inj_neighbor w hwr hwn a' b ha'_lt hbn hwa' hwb hne hturn)
  rw [← heq_ab]
  exact haa'

/-- Bidirectional version of `matchesConfCycle_adj_of_step` for either orientation step. -/
theorem matchesConfCycle_adj_of_nodePerm_step
    (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hmc : MatchesConfCycle (parsedRConfList[h]'hlen) H.dual darts p.emb)
    {w a b : Nat}
    (hwr : (configOfRConf (parsedRConfList[h]'hlen)).ringSize ≤ w)
    (hwn : w < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes)
    (han : a < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes)
    (hbn : b < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes)
    (hwa : (configOfRConf (parsedRConfList[h]'hlen)).adj w a = true)
    (hwb : (configOfRConf (parsedRConfList[h]'hlen)).adj w b = true)
    (hstep : (nodePermOriented H.dual p.emb.orient).f (p.emb.dart w a) = p.emb.dart w b ∨
             (nodePermOriented H.dual p.emb.orient).inv (p.emb.dart w a) = p.emb.dart w b) :
    (configOfRConf (parsedRConfList[h]'hlen)).adj a b = true := by
  rcases hstep with hf | hi
  · exact matchesConfCycle_adj_of_step h hh hlen darts p hmc hwr hwn han hbn hwa hwb hf
  · have hf' : (nodePermOriented H.dual p.emb.orient).f (p.emb.dart w b) = p.emb.dart w a := by
      have hg := congrArg (nodePermOriented H.dual p.emb.orient).f hi
      rw [(nodePermOriented H.dual p.emb.orient).right_inv] at hg
      exact hg.symm
    have hba := matchesConfCycle_adj_of_step h hh hlen darts p hmc hwr hwn hbn han hwb hwa hf'
    rw [p.adj_symm a b han hbn]
    exact hba

/-- Pairwise injectivity of `p.emb.rep` in `H.dual` on all endpoints of `contractEdges`:
    no two distinct `u ≠ v` in `ceVerts c.contractEdges` can collide in `H.dual`, ruling out
    both length-1, length-2, and length-3 dual-pinch shortcuts via bridgelessness, `mc_dual_no_parallel`,
    and `mc_three_cycle_consecutive` + `MatchesConfCycle`. -/
theorem vx_rep_distinct_in_dual
    (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hmc : MatchesConfCycle (parsedRConfList[h]'hlen) H.dual darts p.emb)
    {u v : Nat}
    (hu_ce : u ∈ ceVerts (configOfRConf (parsedRConfList[h]'hlen)).contractEdges)
    (hv_ce : v ∈ ceVerts (configOfRConf (parsedRConfList[h]'hlen)).contractEdges)
    (hun : u < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes)
    (hvn : v < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes)
    (hne : u ≠ v) :
    sameVertex H.dual (p.emb.rep u) (p.emb.rep v) darts.length = false := by
  let c := configOfRConf (parsedRConfList[h]'hlen)
  by_cases hur : c.ringSize ≤ u <;> by_cases hvr : c.ringSize ≤ v
  · exact p.emb.int_distinct u v hur hun hvr hvn hne
  · exact p.emb.int_ring_distinct u v hur hun (Nat.lt_of_not_le hvr)
  · have hi := p.emb.int_ring_distinct v u hvr hvn (Nat.lt_of_not_le hur)
    rw [sameVertex_symm_of_complete H.dual darts h_mc.complete (Nat.le_refl _)]
    exact hi
  · have hu_r : u < c.ringSize := Nat.lt_of_not_le hur
    have hv_r : v < c.ringSize := Nat.lt_of_not_le hvr
    have aux : ∀ x y, x ∈ ceVerts c.contractEdges → y ∈ ceVerts c.contractEdges →
        x < c.ringSize → y < c.ringSize → x < y →
        sameVertex H.dual (p.emb.rep x) (p.emb.rep y) darts.length = false := by
      intro x y hx_ce hy_ce hxr hyr hxy
      have hxn : x < c.totalNodes := Nat.lt_of_lt_of_le hxr (Nat.le_add_right _ _)
      have hyn : y < c.totalNodes := Nat.lt_of_lt_of_le hyr (Nat.le_add_right _ _)
      have hdist := (rConf_forest_props h hh hlen).2.2.2 x y hx_ce hy_ce hxr hyr hxy
      have dist2_absurd : ∀ w, c.ringSize ≤ w → w < c.totalNodes →
          c.adj w x = true → c.adj w y = true →
          sameVertex H.dual (p.emb.rep x) (p.emb.rep y) darts.length = true → False := by
        intro w hwr hwn hwx hwy hsv_xy
        have hs1 : sameVertex H.dual (p.emb.dart w x) (p.emb.dart w y) darts.length = true :=
          dual_sameVertex_trans darts h_mc
            (p.emb.dart_same_vertex_rep w hwr hwn x hxn hwx)
            (dual_sameVertex_symm darts h_mc (p.emb.dart_same_vertex_rep w hwr hwn y hyn hwy))
        have hs2 : sameVertex H.dual (H.edge.f (p.emb.dart w x)) (H.edge.f (p.emb.dart w y)) darts.length = true := by
          change sameVertex H.dual (H.dual.edge.f (p.emb.dart w x)) (H.dual.edge.f (p.emb.dart w y)) darts.length = true
          exact dual_sameVertex_trans darts h_mc
            (p.emb.dart_edge_same_vertex_rep w hwr hwn x hxn hwx)
            (dual_sameVertex_trans darts h_mc hsv_xy
              (dual_sameVertex_symm darts h_mc (p.emb.dart_edge_same_vertex_rep w hwr hwn y hyn hwy)))
        have hd_eq := mc_dual_no_parallel darts h_mc hs1 hs2
        exact p.emb.int_inj_neighbor w hwr hwn x y hxn hyn hwx hwy (by omega) hd_eq
      rcases hdist with h1 | ⟨w, hwr, hwn, hwx, hwy⟩ | ⟨w1, w2, hw1r, hw1n, hw2r, hw2n, hw12, hw1x, hw12a, hw2y⟩
      · exact adj_ne_vertex darts h_mc (p.emb.adj_rep_edge x y hxn hyn h1)
      · cases hs : sameVertex H.dual (p.emb.rep x) (p.emb.rep y) darts.length
        · rfl
        · exact False.elim (dist2_absurd w hwr hwn hwx hwy hs)
      · cases hs : sameVertex H.dual (p.emb.rep x) (p.emb.rep y) darts.length
        · rfl
        · exfalso
          have h12_sv : sameVertex H.dual (p.emb.rep w1) (p.emb.rep w2) darts.length = false :=
            p.emb.int_distinct w1 w2 hw1r hw1n hw2r hw2n hw12
          have h1x_sv : sameVertex H.dual (p.emb.rep w1) (p.emb.rep x) darts.length = false :=
            p.emb.int_ring_distinct w1 x hw1r hw1n hxr
          have h2x_sv : sameVertex H.dual (p.emb.rep w2) (p.emb.rep x) darts.length = false :=
            p.emb.int_ring_distinct w2 x hw2r hw2n hxr
          have hxw2 : sameVertex H.dual (p.emb.rep x) (p.emb.rep w2) darts.length = false := by
            cases hres : sameVertex H.dual (p.emb.rep x) (p.emb.rep w2) darts.length
            · rfl
            · rw [dual_sameVertex_symm darts h_mc hres] at h2x_sv; cases h2x_sv
          have hadj_x_w2 : areAdjacentVertices H.dual (p.emb.rep x) (p.emb.rep w2) darts.length = true := by
            apply areAdjacentVertices_of_dart H.dual darts h_mc.complete (Nat.le_refl _)
            · exact dual_sameVertex_trans darts h_mc
                (p.emb.dart_edge_same_vertex_rep w2 hw2r hw2n y hyn hw2y)
                (dual_sameVertex_symm darts h_mc hs)
            · rw [H.dual.edge_edge (p.emb.dart w2 y)]
              exact p.emb.dart_same_vertex_rep w2 hw2r hw2n y hyn hw2y
          have hstep := mc_three_cycle_consecutive darts h_mc p.emb.orient h1x_sv hxw2
            (by cases hres : sameVertex H.dual (p.emb.rep w2) (p.emb.rep w1) darts.length
                · rfl
                · rw [dual_sameVertex_symm darts h_mc hres] at h12_sv; cases h12_sv)
            (p.emb.dart_same_vertex_rep w1 hw1r hw1n x hxn hw1x)
            (p.emb.dart_edge_same_vertex_rep w1 hw1r hw1n x hxn hw1x)
            (p.emb.dart_same_vertex_rep w1 hw1r hw1n w2 hw2n hw12a)
            (p.emb.dart_edge_same_vertex_rep w1 hw1r hw1n w2 hw2n hw12a)
            hadj_x_w2
          have hadj_xw2 := matchesConfCycle_adj_of_nodePerm_step h hh hlen darts p hmc
            hw1r hw1n hxn hw2n hw1x hw12a hstep
          have hadj_w2x : c.adj w2 x = true := by
            rw [p.adj_symm w2 x hw2n hxn]; exact hadj_xw2
          exact dist2_absurd w2 hw2r hw2n hadj_w2x hw2y hs
    rcases Nat.lt_trichotomy u v with huv | rfl | hvu
    · exact aux u v hu_ce hv_ce hu_r hv_r huv
    · exact absurd rfl hne
    · rw [sameVertex_symm_of_complete H.dual darts h_mc.complete (Nat.le_refl _)]
      exact aux v u hv_ce hu_ce hv_r hu_r hvu

/-- Converse form of `vx_rep_distinct_in_dual`: colliding contract endpoints must be equal. -/
theorem vx_rep_sameVertex_eq_of_mem_ceVerts
    (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hmc : MatchesConfCycle (parsedRConfList[h]'hlen) H.dual darts p.emb)
    {u v : Nat}
    (hu_ce : u ∈ ceVerts (configOfRConf (parsedRConfList[h]'hlen)).contractEdges)
    (hv_ce : v ∈ ceVerts (configOfRConf (parsedRConfList[h]'hlen)).contractEdges)
    (hun : u < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes)
    (hvn : v < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes)
    (hsv : sameVertex H.dual (p.emb.rep u) (p.emb.rep v) darts.length = true) :
    u = v := by
  by_cases huv : u = v
  · exact huv
  · have hf := vx_rep_distinct_in_dual h hh hlen darts h_mc p hmc hu_ce hv_ce hun hvn huv
    rw [hsv] at hf
    cases hf

/-- Canonical endpoint pair specification for every edge `q ∈ c.contractEdges`. -/
theorem contractEdgeDart_spec
    {c : Configuration} {T : Hypermap} [DecidableEq T.Dart] {darts : List T.Dart}
    (p : CorrespondingProjection c T darts) {q : Nat × Nat} (hq : q ∈ c.contractEdges) :
    let qA := if c.ringSize ≤ q.1 then q.1 else q.2
    let qB := if c.ringSize ≤ q.1 then q.2 else q.1
    c.ringSize ≤ qA ∧ qA < c.totalNodes ∧ qB < c.totalNodes ∧ c.adj qA qB = true ∧
    qA ∈ ceVerts c.contractEdges ∧ qB ∈ ceVerts c.contractEdges ∧
    ((qA = q.1 ∧ qB = q.2) ∨ (qA = q.2 ∧ qB = q.1)) ∧
    contractEdgeDart p.emb q = p.emb.dart qA qB := by
  obtain ⟨h1, h2, _, hadj12, hnrr⟩ := p.contract_valid q hq
  by_cases h1r : c.ringSize ≤ q.1
  · simp only [contractEdgeDart, if_pos h1r]
    exact ⟨h1r, h1, h2, hadj12,
      List.mem_flatMap.mpr ⟨q, hq, by simp⟩,
      List.mem_flatMap.mpr ⟨q, hq, by simp⟩,
      by simp, trivial⟩
  · have h2r : c.ringSize ≤ q.2 := by omega
    have hadj21 : c.adj q.2 q.1 = true := by rw [p.adj_symm q.2 q.1 h2 h1]; exact hadj12
    simp only [contractEdgeDart, if_neg h1r]
    exact ⟨h2r, h2, h1, hadj21,
      List.mem_flatMap.mpr ⟨q, hq, by simp⟩,
      List.mem_flatMap.mpr ⟨q, hq, by simp⟩,
      by simp, trivial⟩

private theorem list_nodup_map_on' {α β : Type} (f : α → β) :
    ∀ {l : List α}, (∀ a ∈ l, ∀ b ∈ l, f a = f b → a = b) → l.Nodup → (l.map f).Nodup
  | [], _, _ => List.nodup_nil
  | a :: l, hinj, h => by
    have ha : a ∉ l := (List.nodup_cons.mp h).1
    have hl : l.Nodup := (List.nodup_cons.mp h).2
    have hinj_l : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y := fun x hx y hy =>
      hinj x (List.mem_cons.mpr (Or.inr hx)) y (List.mem_cons.mpr (Or.inr hy))
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, list_nodup_map_on' f hinj_l hl⟩
    intro hm
    rw [List.mem_map] at hm
    obtain ⟨b, hb_mem, hb_eq⟩ := hm
    have hba : b = a :=
      hinj b (List.mem_cons.mpr (Or.inr hb_mem)) a (List.mem_cons.mpr (Or.inl rfl)) hb_eq
    exact ha (hba ▸ hb_mem)

/-- Every mapped contract dart represents a distinct undirected edge in `H`:
    `mappedContractDarts p.emb` is duplicate-free and contains no edge partner `H.edge.f m`. -/
theorem mappedContractDarts_nodup_and_disjoint_rev
    (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hmc : MatchesConfCycle (parsedRConfList[h]'hlen) H.dual darts p.emb) :
    (mappedContractDarts p.emb).Nodup ∧
      ∀ m ∈ mappedContractDarts p.emb, H.edge.f m ∉ mappedContractDarts p.emb := by
  let c := configOfRConf (parsedRConfList[h]'hlen)
  obtain ⟨_, hrev, hnd_ce⟩ := ceNoDupUnordered_spec (rConf_forest_props h hh hlen).1
  refine ⟨?_, ?_⟩
  · dsimp only [mappedContractDarts]
    apply list_nodup_map_on' (contractEdgeDart p.emb) _ hnd_ce
    intro q1 hq1 q2 hq2 heq
    obtain ⟨hq1Ar, hq1An, hq1Bn, hq1Adj, hq1Ace, hq1Bce, hq1or, hq1d⟩ := contractEdgeDart_spec p hq1
    obtain ⟨hq2Ar, hq2An, hq2Bn, hq2Adj, hq2Ace, hq2Bce, hq2or, hq2d⟩ := contractEdgeDart_spec p hq2
    let q1A := if c.ringSize ≤ q1.1 then q1.1 else q1.2
    let q1B := if c.ringSize ≤ q1.1 then q1.2 else q1.1
    let q2A := if c.ringSize ≤ q2.1 then q2.1 else q2.2
    let q2B := if c.ringSize ≤ q2.1 then q2.2 else q2.1
    change contractEdgeDart p.emb q1 = p.emb.dart q1A q1B at hq1d
    change contractEdgeDart p.emb q2 = p.emb.dart q2A q2B at hq2d
    rw [hq1d, hq2d] at heq
    have hsvA : sameVertex H.dual (p.emb.rep q1A) (p.emb.rep q2A) darts.length = true :=
      dual_sameVertex_trans darts h_mc
        (dual_sameVertex_symm darts h_mc (p.emb.dart_same_vertex_rep q1A hq1Ar hq1An q1B hq1Bn hq1Adj))
        (heq ▸ p.emb.dart_same_vertex_rep q2A hq2Ar hq2An q2B hq2Bn hq2Adj)
    have hsvB : sameVertex H.dual (p.emb.rep q1B) (p.emb.rep q2B) darts.length = true := by
      have hheq := congrArg H.edge.f heq
      exact dual_sameVertex_trans darts h_mc
        (dual_sameVertex_symm darts h_mc (p.emb.dart_edge_same_vertex_rep q1A hq1Ar hq1An q1B hq1Bn hq1Adj))
        (hheq ▸ p.emb.dart_edge_same_vertex_rep q2A hq2Ar hq2An q2B hq2Bn hq2Adj)
    have hA_eq := vx_rep_sameVertex_eq_of_mem_ceVerts h hh hlen darts h_mc p hmc hq1Ace hq2Ace hq1An hq2An hsvA
    have hB_eq := vx_rep_sameVertex_eq_of_mem_ceVerts h hh hlen darts h_mc p hmc hq1Bce hq2Bce hq1Bn hq2Bn hsvB
    rcases hq1or with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;> rcases hq2or with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
    · exact Prod.ext (h1a.symm.trans (hA_eq.trans h2a)) (h1b.symm.trans (hB_eq.trans h2b))
    · exfalso
      have hp2 : (q1.2, q1.1) ∈ c.contractEdges := by
        have hx : q2 = (q1.2, q1.1) := Prod.ext (h2b.symm.trans (hB_eq.symm.trans h1b))
          (h2a.symm.trans (hA_eq.symm.trans h1a))
        exact hx ▸ hq2
      exact hrev q1.1 q1.2 (by simpa using hq1) hp2
    · exfalso
      have hp2 : (q1.2, q1.1) ∈ c.contractEdges := by
        have hx : q2 = (q1.2, q1.1) := Prod.ext (h2a.symm.trans (hA_eq.symm.trans h1a))
          (h2b.symm.trans (hB_eq.symm.trans h1b))
        exact hx ▸ hq2
      exact hrev q1.1 q1.2 (by simpa using hq1) hp2
    · exact Prod.ext (h1b.symm.trans (hB_eq.trans h2b)) (h1a.symm.trans (hA_eq.trans h2a))
  · intro m hm hedm
    rw [mappedContractDarts, List.mem_map] at hm hedm
    obtain ⟨q1, hq1, hq1m⟩ := hm
    obtain ⟨q2, hq2, hq2ed⟩ := hedm
    obtain ⟨hq1Ar, hq1An, hq1Bn, hq1Adj, hq1Ace, hq1Bce, hq1or, hq1d⟩ := contractEdgeDart_spec p hq1
    obtain ⟨hq2Ar, hq2An, hq2Bn, hq2Adj, hq2Ace, hq2Bce, hq2or, hq2d⟩ := contractEdgeDart_spec p hq2
    let q1A := if c.ringSize ≤ q1.1 then q1.1 else q1.2
    let q1B := if c.ringSize ≤ q1.1 then q1.2 else q1.1
    let q2A := if c.ringSize ≤ q2.1 then q2.1 else q2.2
    let q2B := if c.ringSize ≤ q2.1 then q2.2 else q2.1
    change contractEdgeDart p.emb q1 = p.emb.dart q1A q1B at hq1d
    change contractEdgeDart p.emb q2 = p.emb.dart q2A q2B at hq2d
    have heq : H.edge.f (p.emb.dart q1A q1B) = p.emb.dart q2A q2B := by
      rw [← hq1d, ← hq2d, hq1m, hq2ed]
    have hsv1 : sameVertex H.dual (p.emb.rep q1B) (p.emb.rep q2A) darts.length = true :=
      dual_sameVertex_trans darts h_mc
        (dual_sameVertex_symm darts h_mc (p.emb.dart_edge_same_vertex_rep q1A hq1Ar hq1An q1B hq1Bn hq1Adj))
        (heq ▸ p.emb.dart_same_vertex_rep q2A hq2Ar hq2An q2B hq2Bn hq2Adj)
    have hq1B_eq_q2A := vx_rep_sameVertex_eq_of_mem_ceVerts h hh hlen darts h_mc p hmc
      hq1Bce hq2Ace hq1Bn hq2An hsv1
    have heq' : p.emb.dart q1A q1B = H.edge.f (p.emb.dart q2A q2B) := by
      rw [← heq, H.edge_edge]
    have hsv2 : sameVertex H.dual (p.emb.rep q1A) (p.emb.rep q2B) darts.length = true :=
      dual_sameVertex_trans darts h_mc
        (dual_sameVertex_symm darts h_mc (p.emb.dart_same_vertex_rep q1A hq1Ar hq1An q1B hq1Bn hq1Adj))
        (heq' ▸ p.emb.dart_edge_same_vertex_rep q2A hq2Ar hq2An q2B hq2Bn hq2Adj)
    have hq1A_eq_q2B := vx_rep_sameVertex_eq_of_mem_ceVerts h hh hlen darts h_mc p hmc
      hq1Ace hq2Bce hq1An hq2Bn hsv2
    by_cases hqq : q1 = q2
    · subst hqq
      have hbad : m = H.edge.f m := hq1m.symm.trans hq2ed
      exact mc_edge_ne_self H darts h_mc m hbad.symm
    · rcases hq1or with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;> rcases hq2or with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
      · have hp2 : (q1.2, q1.1) ∈ c.contractEdges := by
          have hx : q2 = (q1.2, q1.1) := Prod.ext (h2a.symm.trans (hq1B_eq_q2A.symm.trans h1b))
            (h2b.symm.trans (hq1A_eq_q2B.symm.trans h1a))
          exact hx ▸ hq2
        exact hrev q1.1 q1.2 (by simpa using hq1) hp2
      · exact hqq (Prod.ext (h1a.symm.trans (hq1A_eq_q2B.trans h2b)) (h1b.symm.trans (hq1B_eq_q2A.trans h2a)))
      · exact hqq (Prod.ext (h1b.symm.trans (hq1B_eq_q2A.trans h2a)) (h1a.symm.trans (hq1A_eq_q2B.trans h2b)))
      · have hp2 : (q1.2, q1.1) ∈ c.contractEdges := by
          have hx : q2 = (q1.2, q1.1) := Prod.ext (h2b.symm.trans (hq1A_eq_q2B.symm.trans h1a))
            (h2a.symm.trans (hq1B_eq_q2A.symm.trans h1b))
          exact hx ▸ hq2
        exact hrev q1.1 q1.2 (by simpa using hq1) hp2

/-- Endpoint characterization for any `d` appearing in `mappedContractDarts p.emb`. -/
theorem mem_mappedContractDarts_endpoints
    (h : Nat) (_hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact _hh)
    {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    {m : H.Dart} (hm : m ∈ mappedContractDarts p.emb) :
    ∃ qA qB,
      let c := configOfRConf (parsedRConfList[h]'hlen)
      c.ringSize ≤ qA ∧ qA < c.totalNodes ∧ qB < c.totalNodes ∧ c.adj qA qB = true ∧
      isContractEdge c.contractEdges qA qB = true ∧
      qA ∈ ceVerts c.contractEdges ∧ qB ∈ ceVerts c.contractEdges ∧
      m = p.emb.dart qA qB ∧
      sameVertex H.dual m (p.emb.rep qA) darts.length = true ∧
      sameVertex H.dual (H.edge.f m) (p.emb.rep qB) darts.length = true := by
  rw [mappedContractDarts, List.mem_map] at hm
  obtain ⟨q, hq_mem, rfl⟩ := hm
  obtain ⟨hqAr, hqAn, hqBn, hqAdj, hqAce, hqBce, hqor, hqd⟩ := contractEdgeDart_spec p hq_mem
  let c := configOfRConf (parsedRConfList[h]'hlen)
  let qA := if c.ringSize ≤ q.1 then q.1 else q.2
  let qB := if c.ringSize ≤ q.1 then q.2 else q.1
  change contractEdgeDart p.emb q = p.emb.dart qA qB at hqd
  have hce : isContractEdge c.contractEdges qA qB = true := by
    rcases hqor with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · simp only [isContractEdge, Bool.or_eq_true, List.contains_iff_mem]
      left; change qA = q.1 at ha; change qB = q.2 at hb; rw [ha, hb]; exact hq_mem
    · simp only [isContractEdge, Bool.or_eq_true, List.contains_iff_mem]
      right; change qA = q.2 at ha; change qB = q.1 at hb; rw [ha, hb]; exact hq_mem
  refine ⟨qA, qB, hqAr, hqAn, hqBn, hqAdj, hce, hqAce, hqBce, hqd, ?_, ?_⟩
  · rw [hqd]; exact p.emb.dart_same_vertex_rep qA hqAr hqAn qB hqBn hqAdj
  · rw [hqd]
    change sameVertex H.dual (H.dual.edge.f (p.emb.dart qA qB)) (p.emb.rep qB) darts.length = true
    exact p.emb.dart_edge_same_vertex_rep qA hqAr hqAn qB hqBn hqAdj

end DualVertexInjectivity

/-! ## Section 3: Contract Quotient Equivalence & Max-Path Length Bound (`≤ 3`) -/

section ContractQuotientEquivalence

/-- Symmetric dart list deleted when contracting every edge in `mappedContractDarts e`. -/
def contractSymDarts {c : Configuration} {T : Hypermap} [DecidableEq T.Dart]
    {darts : List T.Dart} (e : TriangulationEmbedding c T darts) : List T.Dart :=
  (mappedContractDarts e).flatMap fun m => [m, T.edge.f m]

theorem mem_contractSymDarts_iff {c : Configuration} {T : Hypermap} [DecidableEq T.Dart]
    {darts : List T.Dart} (e : TriangulationEmbedding c T darts) (d : T.Dart) :
    d ∈ contractSymDarts e ↔ ∃ m ∈ mappedContractDarts e, d = m ∨ d = T.edge.f m := by
  simp [contractSymDarts]

theorem contractSymDarts_edge_closed {c : Configuration} {T : Hypermap} [DecidableEq T.Dart]
    {darts : List T.Dart} (e : TriangulationEmbedding c T darts) :
    ∀ d : T.Dart, d ∈ contractSymDarts e ↔ T.edge.f d ∈ contractSymDarts e := by
  intro d
  simp only [mem_contractSymDarts_iff]
  constructor
  · rintro ⟨m, hm, rfl | rfl⟩
    · exact ⟨d, hm, Or.inr rfl⟩
    · refine ⟨m, hm, Or.inl (T.edge_edge m)⟩
  · rintro ⟨m, hm, h1 | h1⟩
    · exact ⟨m, hm, Or.inr (by rw [← h1, T.edge_edge])⟩
    · exact ⟨m, hm, Or.inl (by
        have hi := congrArg T.edge.f h1
        simpa [T.edge_edge] using hi)⟩

/-- Equivalence relation on primal darts generated by `H.face`-orbits and contract edges `M`. -/
inductive ContractFaceEquiv (H : Hypermap) (M : List H.Dart) : H.Dart → H.Dart → Prop where
  | face {x y : H.Dart} : SameOrbit H.face x y → ContractFaceEquiv H M x y
  | edge {m : H.Dart} : m ∈ M → ContractFaceEquiv H M m (H.edge.f m)
  | edge_rev {m : H.Dart} : m ∈ M → ContractFaceEquiv H M (H.edge.f m) m
  | trans {x y z : H.Dart} :
      ContractFaceEquiv H M x y → ContractFaceEquiv H M y z → ContractFaceEquiv H M x z

theorem contractFaceEquiv_refl (H : Hypermap) (M : List H.Dart) (x : H.Dart) :
    ContractFaceEquiv H M x x :=
  ContractFaceEquiv.face ⟨0, rfl⟩

theorem contractFaceEquiv_symm {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts) (M : List H.Dart) {x y : H.Dart}
    (hxy : ContractFaceEquiv H M x y) : ContractFaceEquiv H M y x := by
  induction hxy with
  | face h => exact ContractFaceEquiv.face (sameOrbit_face_symm darts h_mc h)
  | edge hm => exact ContractFaceEquiv.edge_rev hm
  | edge_rev hm => exact ContractFaceEquiv.edge hm
  | trans _ _ ih1 ih2 => exact ContractFaceEquiv.trans ih2 ih1

theorem contractFaceEquiv_nil_iff {H : Hypermap} (x y : H.Dart) :
    ContractFaceEquiv H [] x y ↔ SameOrbit H.face x y := by
  constructor
  · intro h
    induction h with
    | face hxy => exact hxy
    | edge hm => cases hm
    | edge_rev hm => cases hm
    | trans _ _ ih1 ih2 => exact sameOrbit_trans H.face ih1 ih2
  · exact ContractFaceEquiv.face

/-- Right-appended walk version of `ContractFaceEquiv` for single-step structural induction. -/
inductive ContractFaceWalk (H : Hypermap) (M : List H.Dart) (x : H.Dart) : H.Dart → Prop where
  | start : ContractFaceWalk H M x x
  | step_face {y z : H.Dart} :
      ContractFaceWalk H M x y → SameOrbit H.face y z → ContractFaceWalk H M x z
  | step_edge {y m : H.Dart} :
      ContractFaceWalk H M x y → m ∈ M → y = m → ContractFaceWalk H M x (H.edge.f m)
  | step_edge_rev {y m : H.Dart} :
      ContractFaceWalk H M x y → m ∈ M → y = H.edge.f m → ContractFaceWalk H M x m

theorem contractFaceWalk_trans {H : Hypermap} {M : List H.Dart} {x y z : H.Dart}
    (hxy : ContractFaceWalk H M x y) (hyz : ContractFaceWalk H M y z) :
    ContractFaceWalk H M x z := by
  induction hyz with
  | start => exact hxy
  | step_face _ h_f ih => exact ContractFaceWalk.step_face ih h_f
  | step_edge _ hm h_eq ih => exact ContractFaceWalk.step_edge ih hm h_eq
  | step_edge_rev _ hm h_eq ih => exact ContractFaceWalk.step_edge_rev ih hm h_eq

theorem contractFaceEquiv_to_walk {H : Hypermap} {M : List H.Dart} {x y : H.Dart}
    (h : ContractFaceEquiv H M x y) : ContractFaceWalk H M x y := by
  induction h with
  | face hxy => exact ContractFaceWalk.step_face ContractFaceWalk.start hxy
  | edge hm => exact ContractFaceWalk.step_edge ContractFaceWalk.start hm rfl
  | edge_rev hm => exact ContractFaceWalk.step_edge_rev ContractFaceWalk.start hm rfl
  | trans _ _ ih1 ih2 => exact contractFaceWalk_trans ih1 ih2

/-- Undirected edge relation realized by a sub-list `L_M ⊆ mappedContractDarts p.emb`. -/
def subContractEdge {c : Configuration} {T : Hypermap} [DecidableEq T.Dart] {darts : List T.Dart}
    (e : TriangulationEmbedding c T darts) (L_M : List T.Dart) (u v : Nat) : Prop :=
  u < c.totalNodes ∧ v < c.totalNodes ∧ u ≠ v ∧ isContractEdge c.contractEdges u v = true ∧
  ∃ q ∈ c.contractEdges, contractEdgeDart e q ∈ L_M ∧ ((q.1 = u ∧ q.2 = v) ∨ (q.1 = v ∧ q.2 = u))

theorem subContractEdge_symm {c : Configuration} {T : Hypermap} [DecidableEq T.Dart]
    {darts : List T.Dart} {e : TriangulationEmbedding c T darts} {L_M : List T.Dart}
    {u v : Nat} (h : subContractEdge e L_M u v) : subContractEdge e L_M v u := by
  rcases h with ⟨hu, hv, hne, hce, q, hqm, hqd, hqp⟩
  refine ⟨hv, hu, hne.symm, (by rw [isContractEdge_symm]; exact hce), q, hqm, hqd, ?_⟩
  rcases hqp with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact Or.inl ⟨h1, h2⟩

theorem subContractEdge_ceVerts {c : Configuration} {T : Hypermap} [DecidableEq T.Dart]
    {darts : List T.Dart} {e : TriangulationEmbedding c T darts} {L_M : List T.Dart}
    {u v : Nat} (h : subContractEdge e L_M u v) :
    u ∈ ceVerts c.contractEdges ∧ v ∈ ceVerts c.contractEdges :=
  mem_ceVerts_of_isContractEdge h.2.2.2.1

/-- Simple non-backtracking path of length `1`, `2`, or `3` in a sub-forest relation `E`. -/
inductive SimpleContractChain (E : Nat → Nat → Prop) : Nat → Nat → Prop where
  | len1 {u v : Nat} : u ≠ v → E u v → SimpleContractChain E u v
  | len2 {u a v : Nat} :
      u ≠ a → a ≠ v → u ≠ v → E u a → E a v → SimpleContractChain E u v
  | len3 {u a b v : Nat} :
      u ≠ a → a ≠ b → b ≠ v → u ≠ b → a ≠ v → u ≠ v →
      E u a → E a b → E b v → SimpleContractChain E u v

theorem simpleContractChain_ne {E : Nat → Nat → Prop} {u v : Nat}
    (h : SimpleContractChain E u v) : u ≠ v := by
  rcases h with ⟨hne, _⟩ | ⟨_, _, hne, _, _⟩ | ⟨_, _, _, _, _, hne, _, _, _⟩ <;> exact hne

set_option linter.unusedVariables false in
/-- Either `x` and `y` lie in the same `H.face`-orbit (`L = 0`), or they sit at the ends
    of a simple contract path of length `L ∈ {1, 2, 3}` in `subContractEdge p.emb L_M`. -/
def ContractPathState (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (L_M : List H.Dart) (x y : H.Dart) : Prop :=
  let c := configOfRConf (parsedRConfList[h]'hlen)
  SameOrbit H.face x y ∨
  ∃ u v, u < c.totalNodes ∧ v < c.totalNodes ∧
    u ∈ ceVerts c.contractEdges ∧ v ∈ ceVerts c.contractEdges ∧
    SameOrbit H.face x (p.emb.rep u) ∧ SameOrbit H.face y (p.emb.rep v) ∧
    SimpleContractChain (subContractEdge p.emb L_M) u v

private theorem dual_sameVertex_of_face {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts) {x y : H.Dart}
    (h : SameOrbit H.face x y) : sameVertex H.dual x y darts.length = true :=
  sameVertex_dual_of_sameOrbit_face darts h_mc h

private theorem face_sameOrbit_of_dual_sv {H : Hypermap} [DecidableEq H.Dart]
    (darts : List H.Dart) (h_mc : H.PrimalMinimalCounterexample darts) {x y : H.Dart}
    (h : sameVertex H.dual x y darts.length = true) : SameOrbit H.face x y :=
  sameOrbit_face_of_sameVertex_dual darts h_mc h

theorem contractPathState_append_subEdge
    (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hmc : MatchesConfCycle (parsedRConfList[h]'hlen) H.dual darts p.emb)
    {L_M : List H.Dart} {x y z : H.Dart} {v1 w1 : Nat}
    (hstate : ContractPathState h hh hlen H darts p L_M x y)
    (he : subContractEdge p.emb L_M v1 w1)
    (hy : SameOrbit H.face y (p.emb.rep v1))
    (hz : SameOrbit H.face z (p.emb.rep w1)) :
    ContractPathState h hh hlen H darts p L_M x z := by
  let c := configOfRConf (parsedRConfList[h]'hlen)
  have hforest := rConf_forest_props h hh hlen
  have hv1n := he.1
  have hw1n := he.2.1
  have hvw1_ne := he.2.2.1
  have hvw1_ce := he.2.2.2.1
  obtain ⟨hv1_ce, hw1_ce⟩ := subContractEdge_ceVerts he
  rcases hstate with hxy | ⟨u, v, hun, hvn, hu_ce, hv_ce, hxu, hyv, hchain⟩
  · refine Or.inr ⟨v1, w1, hv1n, hw1n, hv1_ce, hw1_ce,
      sameOrbit_trans H.face hxy hy, hz, SimpleContractChain.len1 hvw1_ne he⟩
  · have hvv1_f : SameOrbit H.face (p.emb.rep v) (p.emb.rep v1) :=
      sameOrbit_trans H.face (sameOrbit_face_symm darts h_mc hyv) hy
    have hvv1_eq : v = v1 :=
      vx_rep_sameVertex_eq_of_mem_ceVerts h hh hlen darts h_mc p hmc hv_ce hv1_ce hvn hv1n
        (dual_sameVertex_of_face darts h_mc hvv1_f)
    subst hvv1_eq
    rcases hchain with ⟨huv_ne, huv_e⟩ | ⟨hua, hav, huv_ne, hua_e, hav_e⟩ |
      ⟨hua, hab, hbv, hub, hav_ne, huv_ne, hua_e, hab_e, hbv_e⟩
    · by_cases hwu : w1 = u
      · subst hwu
        exact Or.inl (sameOrbit_trans H.face hxu (sameOrbit_face_symm darts h_mc hz))
      · refine Or.inr ⟨u, w1, hun, hw1n, hu_ce, hw1_ce, hxu, hz,
          SimpleContractChain.len2 huv_ne hvw1_ne (Ne.symm hwu) huv_e he⟩
    · rename_i a
      have ha_ce : a ∈ ceVerts c.contractEdges := (subContractEdge_ceVerts hua_e).1 |> fun _ =>
        (subContractEdge_ceVerts hua_e).2
      have han : a < c.totalNodes := hua_e.2.1
      by_cases hwa : w1 = a
      · subst hwa
        exact Or.inr ⟨u, w1, hun, hw1n, hu_ce, hw1_ce, hxu, hz,
          SimpleContractChain.len1 hua hua_e⟩
      · by_cases hwu : w1 = u
        · exfalso
          have hno3 := hforest.2.1 u a v hua_e.2.2.2.1 hav_e.2.2.2.1 hua hav
          rw [← hwu] at hno3
          rw [hvw1_ce] at hno3
          cases hno3
        · refine Or.inr ⟨u, w1, hun, hw1n, hu_ce, hw1_ce, hxu, hz,
            SimpleContractChain.len3 hua hav hvw1_ne huv_ne (Ne.symm hwa) (Ne.symm hwu) hua_e hav_e he⟩
    · rename_i a b
      by_cases hwb : w1 = b
      · subst hwb
        have hb_ce := (subContractEdge_ceVerts hbv_e).1
        have hbn := hbv_e.1
        exact Or.inr ⟨u, w1, hun, hbn, hu_ce, hb_ce, hxu, hz,
          SimpleContractChain.len2 hua hab hub hua_e hab_e⟩
      · exfalso
        exact hforest.2.2.1 u a b v w1
          hua_e.2.2.2.1 hab_e.2.2.2.1 hbv_e.2.2.2.1 hvw1_ce
          hua hab hbv hvw1_ne hub.symm hav_ne.symm hwb

/-- Every path in `ContractFaceEquiv H L_M` (`L_M ⊆ mappedContractDarts p.emb`) reduces to
    either `SameOrbit H.face` or a simple contract path of length `L ∈ {1, 2, 3}`. -/
theorem contractFaceEquiv_to_simple_contract_path
    (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hmc : MatchesConfCycle (parsedRConfList[h]'hlen) H.dual darts p.emb)
    {L_M : List H.Dart} (hsub : ∀ m ∈ L_M, m ∈ mappedContractDarts p.emb)
    {x y : H.Dart} (heq : ContractFaceEquiv H L_M x y) :
    ContractPathState h hh hlen H darts p L_M x y := by
  have hw := contractFaceEquiv_to_walk heq
  clear heq
  induction hw with
  | start => exact Or.inl ⟨0, rfl⟩
  | step_face _ h_f ih =>
    rcases ih with hxy | ⟨u, v, hun, hvn, huc, hvc, hxu, hyv, hchain⟩
    · exact Or.inl (sameOrbit_trans H.face hxy h_f)
    · exact Or.inr ⟨u, v, hun, hvn, huc, hvc, hxu,
        sameOrbit_trans H.face (sameOrbit_face_symm darts h_mc h_f) hyv, hchain⟩
  | @step_edge y1 m _ hm h_ym ih =>
    have hm_M := hsub m hm
    simp only [mappedContractDarts, List.mem_map] at hm_M
    rcases hm_M with ⟨q, hq_mem, hqm⟩
    obtain ⟨hqAr, hqAn, hqBn, hqAdj, hqAce, hqBce, hqor, hqd⟩ := contractEdgeDart_spec p hq_mem
    let c := configOfRConf (parsedRConfList[h]'hlen)
    let qA := if c.ringSize ≤ q.1 then q.1 else q.2
    let qB := if c.ringSize ≤ q.1 then q.2 else q.1
    change contractEdgeDart p.emb q = p.emb.dart qA qB at hqd
    have hqne : qA ≠ qB := by
      intro heq'
      have hirr := (ceNoDupUnordered_spec (rConf_forest_props h hh hlen).1).1
      have hce : isContractEdge c.contractEdges qA qB = true := by
        rcases hqor with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · change qA = q.1 at h1; change qB = q.2 at h2
          simp [isContractEdge, h1, h2]; exact Or.inl hq_mem
        · change qA = q.2 at h1; change qB = q.1 at h2
          simp [isContractEdge, h1, h2]; exact Or.inr hq_mem
      rw [heq'] at hce
      have hbad : isContractEdge c.contractEdges qB qB = false := hirr qB
      rw [hce] at hbad; cases hbad
    have hce : isContractEdge c.contractEdges qA qB = true := by
      rcases hqor with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · change qA = q.1 at h1; change qB = q.2 at h2
        simp [isContractEdge, h1, h2]; exact Or.inl hq_mem
      · change qA = q.2 at h1; change qB = q.1 at h2
        simp [isContractEdge, h1, h2]; exact Or.inr hq_mem
    have hsubE : subContractEdge p.emb L_M qA qB :=
      ⟨hqAn, hqBn, hqne, hce, q, hq_mem, hqm.symm ▸ hm, by
        rcases hqor with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1.symm, h2.symm⟩
        · exact Or.inr ⟨h2.symm, h1.symm⟩⟩
    have hym : SameOrbit H.face y1 (p.emb.rep qA) := by
      rw [h_ym, ← hqm, hqd]
      exact face_sameOrbit_of_dual_sv darts h_mc (p.emb.dart_same_vertex_rep qA hqAr hqAn qB hqBn hqAdj)
    have hzm : SameOrbit H.face (H.edge.f m) (p.emb.rep qB) := by
      rw [← hqm, hqd]
      exact face_sameOrbit_of_dual_sv darts h_mc
        (p.emb.dart_edge_same_vertex_rep qA hqAr hqAn qB hqBn hqAdj)
    exact contractPathState_append_subEdge h hh hlen darts h_mc p hmc ih hsubE hym hzm
  | @step_edge_rev y1 m _ hm h_ym ih =>
    have hm_M := hsub m hm
    simp only [mappedContractDarts, List.mem_map] at hm_M
    rcases hm_M with ⟨q, hq_mem, hqm⟩
    obtain ⟨hqAr, hqAn, hqBn, hqAdj, hqAce, hqBce, hqor, hqd⟩ := contractEdgeDart_spec p hq_mem
    let c := configOfRConf (parsedRConfList[h]'hlen)
    let qA := if c.ringSize ≤ q.1 then q.1 else q.2
    let qB := if c.ringSize ≤ q.1 then q.2 else q.1
    change contractEdgeDart p.emb q = p.emb.dart qA qB at hqd
    have hqne : qA ≠ qB := by
      intro heq'
      have hirr := (ceNoDupUnordered_spec (rConf_forest_props h hh hlen).1).1
      have hce : isContractEdge c.contractEdges qA qB = true := by
        rcases hqor with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · change qA = q.1 at h1; change qB = q.2 at h2
          simp [isContractEdge, h1, h2]; exact Or.inl hq_mem
        · change qA = q.2 at h1; change qB = q.1 at h2
          simp [isContractEdge, h1, h2]; exact Or.inr hq_mem
      rw [heq'] at hce
      have hbad : isContractEdge c.contractEdges qB qB = false := hirr qB
      rw [hce] at hbad; cases hbad
    have hce : isContractEdge c.contractEdges qA qB = true := by
      rcases hqor with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · change qA = q.1 at h1; change qB = q.2 at h2
        simp [isContractEdge, h1, h2]; exact Or.inl hq_mem
      · change qA = q.2 at h1; change qB = q.1 at h2
        simp [isContractEdge, h1, h2]; exact Or.inr hq_mem
    have hsubE : subContractEdge p.emb L_M qB qA :=
      subContractEdge_symm ⟨hqAn, hqBn, hqne, hce, q, hq_mem, hqm.symm ▸ hm, by
        rcases hqor with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1.symm, h2.symm⟩
        · exact Or.inr ⟨h2.symm, h1.symm⟩⟩
    have hym : SameOrbit H.face y1 (p.emb.rep qB) := by
      rw [h_ym, ← hqm, hqd]
      exact face_sameOrbit_of_dual_sv darts h_mc
        (p.emb.dart_edge_same_vertex_rep qA hqAr hqAn qB hqBn hqAdj)
    have hzm : SameOrbit H.face m (p.emb.rep qA) := by
      rw [← hqm, hqd]
      exact face_sameOrbit_of_dual_sv darts h_mc
        (p.emb.dart_same_vertex_rep qA hqAr hqAn qB hqBn hqAdj)
    exact contractPathState_append_subEdge h hh hlen darts h_mc p hmc ih hsubE hym hzm

/-- Before contracting `m ∈ mappedContractDarts p.emb`, no prefix `pref` disjoint from `m`
    can connect `m` to `H.edge.f m` in `ContractFaceEquiv H pref`. -/
theorem not_contractFaceEquiv_prefix_edge
    (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hmc : MatchesConfCycle (parsedRConfList[h]'hlen) H.dual darts p.emb)
    {pref : List H.Dart} (hsub : ∀ x ∈ pref, x ∈ mappedContractDarts p.emb)
    {m : H.Dart} (hm : m ∈ mappedContractDarts p.emb) (hnot : m ∉ pref) :
    ¬ ContractFaceEquiv H pref m (H.edge.f m) := by
  intro hce_mb
  have hst := contractFaceEquiv_to_simple_contract_path h hh hlen darts h_mc p hmc hsub hce_mb
  rcases hst with h_face | ⟨u, v, hun, hvn, hu_ce, hv_ce, hmu, hbv, hchain⟩
  · exact (isBridgeless_iff_no_sameOrbit_face_edge_jcs H darts h_mc.complete).mp
      h_mc.is_bridgeless m h_face
  · simp only [mappedContractDarts, List.mem_map] at hm
    rcases hm with ⟨q, hq_mem, hqm⟩
    obtain ⟨hqAr, hqAn, hqBn, hqAdj, hqAce, hqBce, hqor, hqd⟩ := contractEdgeDart_spec p hq_mem
    let c := configOfRConf (parsedRConfList[h]'hlen)
    let qA := if c.ringSize ≤ q.1 then q.1 else q.2
    let qB := if c.ringSize ≤ q.1 then q.2 else q.1
    change contractEdgeDart p.emb q = p.emb.dart qA qB at hqd
    have hm_qA : SameOrbit H.face m (p.emb.rep qA) := by
      rw [← hqm, hqd]
      exact face_sameOrbit_of_dual_sv darts h_mc
        (p.emb.dart_same_vertex_rep qA hqAr hqAn qB hqBn hqAdj)
    have hbm_qB : SameOrbit H.face (H.edge.f m) (p.emb.rep qB) := by
      rw [← hqm, hqd]
      exact face_sameOrbit_of_dual_sv darts h_mc
        (p.emb.dart_edge_same_vertex_rep qA hqAr hqAn qB hqBn hqAdj)
    have hu_eq : u = qA := vx_rep_sameVertex_eq_of_mem_ceVerts h hh hlen darts h_mc p hmc
      hu_ce hqAce hun hqAn (dual_sameVertex_of_face darts h_mc
        (sameOrbit_trans H.face (sameOrbit_face_symm darts h_mc hmu) hm_qA))
    have hv_eq : v = qB := vx_rep_sameVertex_eq_of_mem_ceVerts h hh hlen darts h_mc p hmc
      hv_ce hqBce hvn hqBn (dual_sameVertex_of_face darts h_mc
        (sameOrbit_trans H.face (sameOrbit_face_symm darts h_mc hbv) hbm_qB))
    subst hu_eq hv_eq
    have hforest := rConf_forest_props h hh hlen
    obtain ⟨_, hrev, _⟩ := ceNoDupUnordered_spec hforest.1
    have hqBA_ce : isContractEdge c.contractEdges qB qA = true := by
      rcases hqor with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · change qA = q.1 at h1; change qB = q.2 at h2
        simp [isContractEdge, h1, h2]; exact Or.inr hq_mem
      · change qA = q.2 at h1; change qB = q.1 at h2
        simp [isContractEdge, h1, h2]; exact Or.inl hq_mem
    rcases hchain with ⟨hne, ⟨_, _, _, _, q', hq'm, hq'd, hq'p⟩⟩ |
      ⟨hua, hav, huv, hua_e, hav_e⟩ | ⟨hua, hab, hbv_ne, hub, hav_ne, huv, hua_e, hab_e, hbv_e⟩
    · have hqq' : q' = q := by
        rcases hqor with ⟨h1a, h1b⟩ | ⟨h1a, h1b⟩ <;> rcases hq'p with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
        · exact Prod.ext (h2a.trans h1a) (h2b.trans h1b)
        · exfalso
          have hq1' : (q.1, q.2) ∈ c.contractEdges := by simpa using hq_mem
          have hq2' : (q.2, q.1) ∈ c.contractEdges := by
            have : q' = (q.2, q.1) := Prod.ext (h2a.trans h1b) (h2b.trans h1a)
            exact this ▸ hq'm
          exact hrev q.1 q.2 hq1' hq2'
        · exfalso
          have hq1' : (q.1, q.2) ∈ c.contractEdges := by simpa using hq_mem
          have hq2' : (q.2, q.1) ∈ c.contractEdges := by
            have : q' = (q.2, q.1) := Prod.ext (h2a.trans h1a) (h2b.trans h1b)
            exact this ▸ hq'm
          exact hrev q.1 q.2 hq1' hq2'
        · exact Prod.ext (h2a.trans h1b) (h2b.trans h1a)
      subst hqq'
      exact hnot (hqm ▸ hq'd)
    · rename_i a
      have hbad := hforest.2.1 qA a qB hua_e.2.2.2.1 hav_e.2.2.2.1 hua hav
      rw [hqBA_ce] at hbad; cases hbad
    · rename_i a b
      exact hforest.2.2.1 qA a b qB qA
        hua_e.2.2.2.1 hab_e.2.2.2.1 hbv_e.2.2.2.1 hqBA_ce
        hua hab hbv_ne huv.symm hub.symm hav_ne.symm hub

end ContractQuotientEquivalence

/-! ## Section 4: `swapCompRight` Face-Merging & `deleteEdgesSubtype` Face-Orbit Equivalence -/

section ContractFaceMerge

private theorem iter_restrictPerm_val' {D : Type} (p : Perm D) (removed : List D)
    (h_inv : ∀ d, d ∈ removed ↔ p.f d ∈ removed) (k : Nat) (x : { d : D // d ∉ removed }) :
    (Perm.iter (restrictPerm p removed h_inv) k x).val = Perm.iter p k x.val := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    rw [Perm.iter_succ, Perm.iter_succ, ← ih x]
    rfl

private theorem sameOrbit_restrictPerm_iff' {D : Type} (p : Perm D) (removed : List D)
    (h_inv : ∀ d, d ∈ removed ↔ p.f d ∈ removed) (u w : { d : D // d ∉ removed }) :
    SameOrbit (restrictPerm p removed h_inv) u w ↔ SameOrbit p u.val w.val := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← iter_restrictPerm_val' p removed h_inv k u, hk]⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, Subtype.ext (by rw [iter_restrictPerm_val' p removed h_inv k u, hk])⟩

/-- Symmetrized merge relation uniting the `a`-class and `b`-class under equivalence relation `R`. -/
def MergedRel {D : Type} (R : D → D → Prop) (a b x y : D) : Prop :=
  R x y ∨ (R x a ∧ R b y) ∨ (R x b ∧ R a y)

theorem mergedRel_refl {D : Type} {R : D → D → Prop} (h_refl : ∀ x, R x x) (a b x : D) :
    MergedRel R a b x x :=
  Or.inl (h_refl x)

theorem mergedRel_symm {D : Type} {R : D → D → Prop} (h_symm : ∀ {x y}, R x y → R y x)
    {a b x y : D} (h : MergedRel R a b x y) : MergedRel R a b y x := by
  rcases h with hxy | ⟨hxa, hby⟩ | ⟨hxb, hay⟩
  · exact Or.inl (h_symm hxy)
  · exact Or.inr (Or.inr ⟨h_symm hby, h_symm hxa⟩)
  · exact Or.inr (Or.inl ⟨h_symm hay, h_symm hxb⟩)

theorem mergedRel_trans {D : Type} {R : D → D → Prop}
    (h_trans : ∀ {x y z}, R x y → R y z → R x z)
    {a b x y z : D} (hxy : MergedRel R a b x y) (hyz : MergedRel R a b y z) :
    MergedRel R a b x z := by
  rcases hxy with h1 | ⟨h1a, h1b⟩ | ⟨h1b, h1a⟩
  · rcases hyz with h2 | ⟨h2a, h2b⟩ | ⟨h2b, h2a⟩
    · exact Or.inl (h_trans h1 h2)
    · exact Or.inr (Or.inl ⟨h_trans h1 h2a, h2b⟩)
    · exact Or.inr (Or.inr ⟨h_trans h1 h2b, h2a⟩)
  · rcases hyz with h2 | ⟨_, h2b⟩ | ⟨_, h2a⟩
    · exact Or.inr (Or.inl ⟨h1a, h_trans h1b h2⟩)
    · exact Or.inr (Or.inl ⟨h1a, h2b⟩)
    · exact Or.inl (h_trans h1a h2a)
  · rcases hyz with h2 | ⟨_, h2b⟩ | ⟨_, h2a⟩
    · exact Or.inr (Or.inr ⟨h1b, h_trans h1a h2⟩)
    · exact Or.inl (h_trans h1b h2b)
    · exact Or.inr (Or.inr ⟨h1b, h2a⟩)

/-- Splitting/merging `SameOrbit` under `swapCompRight p a b` when `a` and `b` lie in
    distinct `p`-orbits: `SameOrbit (swapCompRight p a b)` is the transitive closure merging
    the `a`-orbit and `b`-orbit of `p`. -/
theorem sameOrbit_swapCompRight_iff_of_not_sameOrbit {D : Type} [DecidableEq D]
    (p : Perm D) (darts : List D) (h_all : ∀ d : D, d ∈ darts)
    {a b : D} (h_not : ¬ SameOrbit p a b) (x y : D) :
    SameOrbit (swapCompRight p a b) x y ↔ MergedRel (SameOrbit p) a b x y := by
  let q := swapCompRight p a b
  have h_step_fwd : ∀ z : D, MergedRel (SameOrbit p) a b z (q.f z) := by
    intro z
    by_cases hza : z = a
    · subst hza
      have hqf : q.f z = p.f b := by
        dsimp [q, swapCompRight]
        rw [swapFun_left]
      rw [hqf]
      exact Or.inr (Or.inl ⟨⟨0, rfl⟩, ⟨1, rfl⟩⟩)
    · by_cases hzb : z = b
      · subst hzb
        have hqf : q.f z = p.f a := by
          dsimp [q, swapCompRight]
          rw [swapFun_right]
        rw [hqf]
        exact Or.inr (Or.inr ⟨⟨0, rfl⟩, ⟨1, rfl⟩⟩)
      · have hqf : q.f z = p.f z := by
          dsimp [q, swapCompRight]
          rw [swapFun_of_ne hza hzb]
        rw [hqf]
        exact Or.inl ⟨1, rfl⟩
  constructor
  · rintro ⟨k, rfl⟩
    induction k with
    | zero => exact Or.inl ⟨0, rfl⟩
    | succ k ih =>
      rw [Perm.iter_succ]
      exact @mergedRel_trans D (SameOrbit p) (fun {_ _ _} h1 h2 => sameOrbit_trans p h1 h2)
        a b x (Perm.iter q k x) (q.f (Perm.iter q k x)) ih (h_step_fwd _)
  · intro h_rel
    have h_not_mem : ¬ b ∈ getOrbit p darts.length a := fun hm =>
      h_not ((sameOrbit_iff_mem_getOrbit p darts h_all (Nat.le_refl _) a b).mpr hm)
    have h_mem_q : b ∈ getOrbit q darts.length a :=
      mem_getOrbit_swapCompRight_diff p darts h_all (Nat.le_refl _) h_not_mem
    have hq_ab : SameOrbit q a b :=
      (sameOrbit_iff_mem_getOrbit q darts h_all (Nat.le_refl _) a b).mpr h_mem_q
    have hq_ba : SameOrbit q b a :=
      sameOrbit_symm_of_complete q darts h_all hq_ab
    have h_step_bwd : ∀ z : D, SameOrbit q z (p.f z) := by
      intro z
      by_cases hza : z = a
      · subst hza
        have hqb : q.f b = p.f z := by
          dsimp [q, swapCompRight]
          rw [swapFun_right]
        exact sameOrbit_trans q hq_ab ⟨1, hqb⟩
      · by_cases hzb : z = b
        · subst hzb
          have hqa : q.f a = p.f z := by
            dsimp [q, swapCompRight]
            rw [swapFun_left]
          exact sameOrbit_trans q hq_ba ⟨1, hqa⟩
        · have hqz : q.f z = p.f z := by
            dsimp [q, swapCompRight]
            rw [swapFun_of_ne hza hzb]
          exact ⟨1, hqz⟩
    have hp_to_q : ∀ {u v : D}, SameOrbit p u v → SameOrbit q u v := by
      rintro u v ⟨k, rfl⟩
      induction k with
      | zero => exact ⟨0, rfl⟩
      | succ k ih =>
        rw [Perm.iter_succ]
        exact sameOrbit_trans q ih (h_step_bwd _)
    rcases h_rel with hxy | ⟨hxa, hby⟩ | ⟨hxb, hay⟩
    · exact hp_to_q hxy
    · exact sameOrbit_trans q (sameOrbit_trans q (hp_to_q hxa) hq_ab) (hp_to_q hby)
    · exact sameOrbit_trans q (sameOrbit_trans q (hp_to_q hxb) hq_ba) (hp_to_q hay)

theorem contractFaceEquiv_mono {H : Hypermap} {L1 L2 : List H.Dart}
    (h_sub : ∀ m ∈ L1, m ∈ L2) {x y : H.Dart}
    (h : ContractFaceEquiv H L1 x y) : ContractFaceEquiv H L2 x y := by
  induction h with
  | face hxy => exact ContractFaceEquiv.face hxy
  | edge hm => exact ContractFaceEquiv.edge (h_sub _ hm)
  | edge_rev hm => exact ContractFaceEquiv.edge_rev (h_sub _ hm)
  | trans _ _ ih1 ih2 => exact ContractFaceEquiv.trans ih1 ih2

theorem contractFaceEquiv_append_singleton_iff {H : Hypermap} (pref : List H.Dart)
    (m x y : H.Dart) :
    ContractFaceEquiv H (pref ++ [m]) x y ↔
      MergedRel (ContractFaceEquiv H pref) m (H.edge.f m) x y := by
  constructor
  · intro hxy
    induction hxy with
    | face h => exact Or.inl (ContractFaceEquiv.face h)
    | @edge k hk =>
      simp only [List.mem_append, List.mem_singleton] at hk
      rcases hk with hkp | rfl
      · exact Or.inl (ContractFaceEquiv.edge hkp)
      · exact Or.inr (Or.inl ⟨contractFaceEquiv_refl H pref k, contractFaceEquiv_refl H pref (H.edge.f k)⟩)
    | @edge_rev k hk =>
      simp only [List.mem_append, List.mem_singleton] at hk
      rcases hk with hkp | rfl
      · exact Or.inl (ContractFaceEquiv.edge_rev hkp)
      · exact Or.inr (Or.inr ⟨contractFaceEquiv_refl H pref (H.edge.f k), contractFaceEquiv_refl H pref k⟩)
    | trans _ _ ih1 ih2 =>
      exact mergedRel_trans ContractFaceEquiv.trans ih1 ih2
  · intro hrel
    have hm_mem : m ∈ pref ++ [m] := List.mem_append.mpr (Or.inr List.mem_cons_self)
    have hmono : ∀ {u v : H.Dart}, ContractFaceEquiv H pref u v →
        ContractFaceEquiv H (pref ++ [m]) u v := fun h =>
      contractFaceEquiv_mono (fun _ hz => List.mem_append.mpr (Or.inl hz)) h
    rcases hrel with h | ⟨hxa, hby⟩ | ⟨hxb, hay⟩
    · exact hmono h
    · exact ContractFaceEquiv.trans (hmono hxa)
        (ContractFaceEquiv.trans (ContractFaceEquiv.edge hm_mem) (hmono hby))
    · exact ContractFaceEquiv.trans (hmono hxb)
        (ContractFaceEquiv.trans (ContractFaceEquiv.edge_rev hm_mem) (hmono hay))

theorem deleteEdgesFold_append {D : Type} [DecidableEq D]
    (T : { T' : PermTriple D // ∀ x, T'.e.f (T'.e.f x) = x }) (xs ys : List D) :
    deleteEdgesFold T (xs ++ ys) = deleteEdgesFold (deleteEdgesFold T xs) ys := by
  induction xs generalizing T with
  | nil => rfl
  | cons d ds ih => exact ih _

private def symDartsList {H : Hypermap} (xs : List H.Dart) : List H.Dart :=
  xs.flatMap fun m => [m, H.edge.f m]

private theorem mem_symDartsList_iff {H : Hypermap} (xs : List H.Dart) (d : H.Dart) :
    d ∈ symDartsList xs ↔ ∃ m ∈ xs, d = m ∨ d = H.edge.f m := by
  simp [symDartsList]

private theorem symDartsList_append {H : Hypermap} (xs ys : List H.Dart) :
    symDartsList (xs ++ ys) = symDartsList xs ++ symDartsList ys := by
  simp [symDartsList]

private structure PrefixDelInv (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (pref : List H.Dart) : Prop where
  he_orig :
    ∀ z, z ∉ symDartsList pref →
      (deleteEdgesFold ⟨H.hypermapToTriple, H.edge_involution⟩ (symDartsList pref)).1.e.f z =
        H.edge.f z
  he_done :
    ∀ z, z ∈ symDartsList pref →
      (deleteEdgesFold ⟨H.hypermapToTriple, H.edge_involution⟩ (symDartsList pref)).1.e.f z = z
  hf_iff :
    ∀ x y, x ∉ symDartsList pref → y ∉ symDartsList pref →
      (SameOrbit
        (deleteEdgesFold ⟨H.hypermapToTriple, H.edge_involution⟩ (symDartsList pref)).1.f x y ↔
        ContractFaceEquiv H pref x y)

private theorem prefixDelInv_step
    (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hmc : MatchesConfCycle (parsedRConfList[h]'hlen) H.dual darts p.emb)
    {pref : List H.Dart} (hsub : ∀ x ∈ pref, x ∈ mappedContractDarts p.emb)
    {m : H.Dart} (hm : m ∈ mappedContractDarts p.emb) (hnot : m ∉ pref)
    (hinv : PrefixDelInv h hh hlen H darts p pref) :
    PrefixDelInv h hh hlen H darts p (pref ++ [m]) := by
  let T0 : { T' : PermTriple H.Dart // ∀ x, T'.e.f (T'.e.f x) = x } :=
    ⟨H.hypermapToTriple, H.edge_involution⟩
  let Tp := deleteEdgesFold T0 (symDartsList pref)
  let b := H.edge.f m
  have hnd := mappedContractDarts_nodup_and_disjoint_rev h hh hlen darts h_mc p hmc
  have hm_nrem : m ∉ symDartsList pref := by
    rw [mem_symDartsList_iff]
    rintro ⟨m', hm', rfl | h_eq⟩
    · exact hnot hm'
    · exact hnd.2 m' (hsub m' hm') (h_eq ▸ hm)
  have hb_nrem : b ∉ symDartsList pref := by
    rw [mem_symDartsList_iff]
    rintro ⟨m', hm', h_eq | h_eq⟩
    · have hmb : H.edge.f m = m' := h_eq
      exact hnd.2 m hm (hmb ▸ hsub m' hm')
    · have hi := congrArg H.edge.f h_eq
      simp only [b, H.edge_edge] at hi
      exact hnot (hi ▸ hm')
  have hTe_m : Tp.1.e.f m = b := hinv.he_orig m hm_nrem
  have hTe_b : Tp.1.e.f b = m := by
    rw [hinv.he_orig b hb_nrem]
    exact H.edge_edge m
  have h_free_m : Tp.1.e.f m ≠ m := by
    rw [hTe_m]
    exact mc_edge_ne_self H darts h_mc m
  let T1 := deleteEdgeStepTriple Tp.1 Tp.2 m
  have hT1_e_b : T1.1.e.f b = b := by
    dsimp [T1, deleteEdgeStepTriple]
    rw [if_neg h_free_m]
    dsimp [isolateFixed, uncoupleEdge, swapCompLeft]
    rw [hTe_m, hTe_b]
    exact swapFun_left m b
  have hfold_eq :
      deleteEdgesFold T0 (symDartsList (pref ++ [m])) = T1 := by
    rw [symDartsList_append, deleteEdgesFold_append]
    change deleteEdgesFold Tp [m, b] = T1
    dsimp [deleteEdgesFold]
    change deleteEdgeStepTriple T1.1 T1.2 b = T1
    dsimp [deleteEdgeStepTriple]
    rw [if_pos hT1_e_b]
  have hT1_e_eq : ∀ z, T1.1.e.f z = swapFun m b (Tp.1.e.f z) := by
    intro z
    dsimp [T1, deleteEdgeStepTriple]
    rw [if_neg h_free_m]
    dsimp [isolateFixed, uncoupleEdge, swapCompLeft]
    rw [hTe_m]
  have hT1_f_eq : T1.1.f = bypass (bypass (swapCompRight Tp.1.f m b) m) b := by
    dsimp [T1, deleteEdgeStepTriple]
    rw [if_neg h_free_m]
    dsimp [isolateFixed, uncoupleEdge]
    rw [hTe_m]
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    change (deleteEdgesFold T0 (symDartsList (pref ++ [m]))).1.e.f z = H.edge.f z
    rw [hfold_eq, hT1_e_eq z]
    have hzm : z ≠ m := fun h' => hz (by simp [symDartsList, h'])
    have hzb : z ≠ b := fun h' => hz (by simp [symDartsList, h', b])
    have hz_pref : z ∉ symDartsList pref := fun h' => hz (by
      rw [symDartsList_append]; exact List.mem_append.mpr (Or.inl h'))
    have hTez : Tp.1.e.f z = H.edge.f z := hinv.he_orig z hz_pref
    have hfez_m : Tp.1.e.f z ≠ m := by
      rw [hTez]
      intro h'
      have hi := congrArg H.edge.f h'
      simp only [H.edge_edge] at hi
      exact hzb hi
    have hfez_b : Tp.1.e.f z ≠ b := by
      rw [hTez]
      intro h'
      have hi := congrArg H.edge.f h'
      simp only [b, H.edge_edge] at hi
      exact hzm hi
    rw [swapFun_of_ne hfez_m hfez_b, hTez]
  · intro z hz
    change (deleteEdgesFold T0 (symDartsList (pref ++ [m]))).1.e.f z = z
    rw [hfold_eq, hT1_e_eq z]
    rw [symDartsList_append, List.mem_append] at hz
    rcases hz with hzp | hzm
    · have hzm' : z ≠ m := fun h' => hm_nrem (h' ▸ hzp)
      have hzb' : z ≠ b := fun h' => hb_nrem (h' ▸ hzp)
      have hfez := hinv.he_done z hzp
      rw [hfez, swapFun_of_ne hzm' hzb']
    · simp only [symDartsList, List.flatMap_cons, List.flatMap_nil, List.append_nil,
        List.mem_cons, List.not_mem_nil, or_false] at hzm
      rcases hzm with rfl | rfl
      · rw [hTe_m]; exact swapFun_right z b
      · rw [hTe_b]; exact swapFun_left m b
  · intro x y hx hy
    change SameOrbit (deleteEdgesFold T0 (symDartsList (pref ++ [m]))).1.f x y ↔
      ContractFaceEquiv H (pref ++ [m]) x y
    rw [hfold_eq, hT1_f_eq]
    have hxm : x ≠ m := fun h' => hx (by simp [symDartsList, h'])
    have hxb : x ≠ b := fun h' => hx (by simp [symDartsList, h', b])
    have hym : y ≠ m := fun h' => hy (by simp [symDartsList, h'])
    have hyb : y ≠ b := fun h' => hy (by simp [symDartsList, h', b])
    have hx_pref : x ∉ symDartsList pref := fun h' => hx (by
      rw [symDartsList_append]; exact List.mem_append.mpr (Or.inl h'))
    have hy_pref : y ∉ symDartsList pref := fun h' => hy (by
      rw [symDartsList_append]; exact List.mem_append.mpr (Or.inl h'))
    let f1 := swapCompRight Tp.1.f m b
    have hbv : BypassValid f1 (bypass (bypass f1 m) b) (fun z => (True ∧ z ≠ m) ∧ z ≠ b) :=
      bypassValid_step f1 (bypass f1 m) (fun z => True ∧ z ≠ m)
        (bypassValid_step f1 f1 (fun _ => True) (bypassValid_self f1) m) b
    rw [bypassValid_sameOrbit_iff hbv ⟨⟨trivial, hxm⟩, hxb⟩ ⟨⟨trivial, hym⟩, hyb⟩]
    have h_not_f : ¬ SameOrbit Tp.1.f m b := by
      intro hso
      have hce := (hinv.hf_iff m b hm_nrem hb_nrem).mp hso
      exact not_contractFaceEquiv_prefix_edge h hh hlen darts h_mc p hmc hsub hm hnot hce
    rw [sameOrbit_swapCompRight_iff_of_not_sameOrbit Tp.1.f darts h_mc.complete h_not_f x y]
    have hm1 : MergedRel (SameOrbit Tp.1.f) m b x y ↔
        MergedRel (ContractFaceEquiv H pref) m b x y := by
      dsimp only [MergedRel]
      rw [hinv.hf_iff x y hx_pref hy_pref, hinv.hf_iff x m hx_pref hm_nrem,
        hinv.hf_iff b y hb_nrem hy_pref, hinv.hf_iff x b hx_pref hb_nrem,
        hinv.hf_iff m y hm_nrem hy_pref]
    exact hm1.trans (contractFaceEquiv_append_singleton_iff pref m x y).symm

private theorem prefixDelInv_of_sublist
    (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hmc : MatchesConfCycle (parsedRConfList[h]'hlen) H.dual darts p.emb)
    (pref : List H.Dart) (hnd : pref.Nodup)
    (hsub : ∀ x ∈ pref, x ∈ mappedContractDarts p.emb) :
    PrefixDelInv h hh hlen H darts p pref := by
  have h_aux : ∀ rev : List H.Dart, rev.reverse.Nodup →
      (∀ x ∈ rev.reverse, x ∈ mappedContractDarts p.emb) →
      PrefixDelInv h hh hlen H darts p rev.reverse := by
    intro rev
    induction rev with
    | nil =>
      intro _ _
      refine ⟨fun _ _ => rfl, fun _ hz => by simp [symDartsList] at hz, fun x y _ _ => ?_⟩
      exact (contractFaceEquiv_nil_iff x y).symm
    | cons m rs ih =>
      intro hnd' hsub'
      rw [List.reverse_cons] at hnd' hsub' ⊢
      have hnd_xs : rs.reverse.Nodup := (List.nodup_append.mp hnd').1
      have hnot : m ∉ rs.reverse := by
        intro hmxs
        exact (List.nodup_append.mp hnd').2.2 m hmxs m List.mem_cons_self rfl
      have hsub_xs : ∀ x ∈ rs.reverse, x ∈ mappedContractDarts p.emb := fun x hx =>
        hsub' x (List.mem_append.mpr (Or.inl hx))
      have hm_mem : m ∈ mappedContractDarts p.emb :=
        hsub' m (List.mem_append.mpr (Or.inr List.mem_cons_self))
      exact prefixDelInv_step h hh hlen darts h_mc p hmc hsub_xs hm_mem hnot
        (ih hnd_xs hsub_xs)
  rw [← List.reverse_reverse pref]
  exact h_aux pref.reverse (by simpa using hnd) (by simpa using hsub)

/-- Face-orbit characterization of the contract-deleted subtype hypermap `H'`: two surviving
    darts lie in the same `H'.face`-orbit if and only if their underlying primal darts are
    identified by `ContractFaceEquiv H (mappedContractDarts p.emb)`. -/
theorem deleteEdgesSubtype_sameOrbit_face_iff_contractFaceEquiv
    (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hmc : MatchesConfCycle (parsedRConfList[h]'hlen) H.dual darts p.emb)
    (h_free : ∀ d : H.Dart, H.edge.f d ≠ d := fun d => mc_edge_ne_self H darts h_mc d)
    (x y : (H.deleteEdgesSubtype (contractSymDarts (T := H.dual) p.emb)
      (@contractSymDarts_edge_closed _ H.dual _ darts p.emb) h_free).Dart) :
    SameOrbit (H.deleteEdgesSubtype (contractSymDarts (T := H.dual) p.emb)
      (@contractSymDarts_edge_closed _ H.dual _ darts p.emb) h_free).face x y ↔
      ContractFaceEquiv H (mappedContractDarts (T := H.dual) p.emb) x.val y.val := by
  let M : List H.Dart := mappedContractDarts (T := H.dual) p.emb
  let H' := H.deleteEdgesSubtype (contractSymDarts (T := H.dual) p.emb)
    (@contractSymDarts_edge_closed _ H.dual _ darts p.emb) h_free
  let Tf := (deleteEdgesFold ⟨H.hypermapToTriple, H.edge_involution⟩
    (contractSymDarts (T := H.dual) p.emb)).1
  have hiter : ∀ k (z : H'.Dart), (Perm.iter H'.face k z).val = Perm.iter Tf.f k z.val := by
    intro k
    induction k with
    | zero => intro _; rfl
    | succ k ih =>
      intro z
      rw [Perm.iter_succ, Perm.iter_succ]
      change Tf.f.f (Perm.iter H'.face k z).val = _
      rw [ih z]
  have hiff1 : SameOrbit H'.face x y ↔ SameOrbit Tf.f x.val y.val := by
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, by rw [← hiter k x, hk]⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext (by rw [hiter k x, hk])⟩
  have hnd := (mappedContractDarts_nodup_and_disjoint_rev h hh hlen darts h_mc p hmc).1
  have hinv := prefixDelInv_of_sublist h hh hlen darts h_mc p hmc M hnd (fun _ hz => hz)
  have h_rem_eq : symDartsList M = contractSymDarts p.emb := rfl
  have hx' : x.val ∉ symDartsList M := by rw [h_rem_eq]; exact x.property
  have hy' : y.val ∉ symDartsList M := by rw [h_rem_eq]; exact y.property
  exact hiff1.trans (hinv.hf_iff x.val y.val hx' hy')

end ContractFaceMerge

/-! ## Section 5: Bridgelessness of Contract-Deleted Subtype & `VertexColoringMod` Existence -/

section ContractDeletedColoring

private theorem isContractEdge_implies_adj_lt
    (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    {x y : Nat}
    (hce : isContractEdge (configOfRConf (parsedRConfList[h]'hlen)).contractEdges x y = true) :
    x < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes ∧
      y < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes ∧
      (configOfRConf (parsedRConfList[h]'hlen)).adj x y = true := by
  have _ := hh
  simp only [isContractEdge, Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hce
  rcases hce with hxy | hyx
  · obtain ⟨hqAr, hqAn, hqBn, hqAdj, _, _, hqor, _⟩ := contractEdgeDart_spec p hxy
    rcases hqor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hxn : x < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes := by simpa [h1] using hqAn
      have hyn : y < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes := by simpa [h2] using hqBn
      exact ⟨hxn, hyn, by simpa [h1, h2] using hqAdj⟩
    · have hxn : x < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes := by simpa [h2] using hqBn
      have hyn : y < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes := by simpa [h1] using hqAn
      have hadj : (configOfRConf (parsedRConfList[h]'hlen)).adj y x = true := by simpa [h1, h2] using hqAdj
      rw [p.adj_symm x y hxn hyn]
      exact ⟨hxn, hyn, hadj⟩
  · obtain ⟨hqAr, hqAn, hqBn, hqAdj, _, _, hqor, _⟩ := contractEdgeDart_spec p hyx
    rcases hqor with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hxn : x < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes := by simpa [h2] using hqBn
      have hyn : y < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes := by simpa [h1] using hqAn
      have hadj : (configOfRConf (parsedRConfList[h]'hlen)).adj y x = true := by simpa [h1, h2] using hqAdj
      rw [p.adj_symm x y hxn hyn]
      exact ⟨hxn, hyn, hadj⟩
    · have hxn : x < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes := by simpa [h1] using hqAn
      have hyn : y < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes := by simpa [h2] using hqBn
      exact ⟨hxn, hyn, by simpa [h1, h2] using hqAdj⟩

/-- Any contract-forest vertex of degree `≥ 2` in `c.contractEdges` is an interior vertex
    (`c.ringSize ≤ w`), because `p.contract_ring_deg` bounds ring vertices to degree `≤ 1`. -/
theorem ceVert_deg_ge_two_is_int
    (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    {u w v : Nat} (huv : u ≠ v)
    (huw : isContractEdge (configOfRConf (parsedRConfList[h]'hlen)).contractEdges u w = true)
    (hwv : isContractEdge (configOfRConf (parsedRConfList[h]'hlen)).contractEdges w v = true) :
    (configOfRConf (parsedRConfList[h]'hlen)).ringSize ≤ w := by
  let c := configOfRConf (parsedRConfList[h]'hlen)
  exact Classical.byContradiction fun hlt => by
    have hwr : w < c.ringSize := Nat.lt_of_not_le hlt
    have hforest := rConf_forest_props h hh hlen
    obtain ⟨hirr, _, hnd_ce⟩ := ceNoDupUnordered_spec hforest.1
    have huw_ne : u ≠ w := by
      intro rfl
      have hbad := hirr u
      rw [huw] at hbad; cases hbad
    have hwv_ne : w ≠ v := by
      intro rfl
      have hbad := hirr w
      rw [hwv] at hbad; cases hbad
    let filt := c.contractEdges.filter (fun q => q.1 == w || q.2 == w)
    have h1 : ∃ q1 ∈ filt, (q1.1 = u ∧ q1.2 = w) ∨ (q1.1 = w ∧ q1.2 = u) := by
      simp only [isContractEdge, Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq] at huw
      rcases huw with hmem | hmem
      · refine ⟨(u, w), List.mem_filter.mpr ⟨hmem, by simp⟩, Or.inl ⟨rfl, rfl⟩⟩
      · refine ⟨(w, u), List.mem_filter.mpr ⟨hmem, by simp⟩, Or.inr ⟨rfl, rfl⟩⟩
    have h2 : ∃ q2 ∈ filt, (q2.1 = w ∧ q2.2 = v) ∨ (q2.1 = v ∧ q2.2 = w) := by
      simp only [isContractEdge, Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq] at hwv
      rcases hwv with hmem | hmem
      · refine ⟨(w, v), List.mem_filter.mpr ⟨hmem, by simp⟩, Or.inl ⟨rfl, rfl⟩⟩
      · refine ⟨(v, w), List.mem_filter.mpr ⟨hmem, by simp⟩, Or.inr ⟨rfl, rfl⟩⟩
    obtain ⟨q1, hq1_mem, hq1_p⟩ := h1
    obtain ⟨q2, hq2_mem, hq2_p⟩ := h2
    have hq_ne : q1 ≠ q2 := by
      intro heq
      subst heq
      rcases hq1_p with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hq2_p with ⟨h2a, h2b⟩ | ⟨h2a, h2b⟩
      · exact huw_ne h2a
      · exact huv h2a
      · exact huv h2b
      · exact hwv_ne h2a
    have h_mem_erase : q2 ∈ filt.erase q1 := (List.mem_erase_of_ne hq_ne.symm).mpr hq2_mem
    have h_len_pos : 0 < (filt.erase q1).length := List.length_pos_of_mem h_mem_erase
    have h_len_eq := List.length_erase_of_mem hq1_mem
    have h_two : 2 ≤ filt.length := by omega
    have h_deg := p.contract_ring_deg w hwr
    dsimp [c, filt] at h_two
    exact Nat.not_le_of_gt h_two h_deg

/-- No two vertices at distance `2` in `c.contractEdges` (`u - a - v`) can be joined by
    an edge in `H.dual`, because `a` is interior, `mc_three_cycle_consecutive` + `MatchesConfCycle`
    would force `c.adj u v = true`, and `p.contract_no_shortcut` would create a contract 3-cycle. -/
theorem mc_dual_L2_adj_impossible
    (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hmc : MatchesConfCycle (parsedRConfList[h]'hlen) H.dual darts p.emb)
    {u a v : Nat} (hua : u ≠ a) (hav : a ≠ v) (huv : u ≠ v)
    (hua_ce : isContractEdge (configOfRConf (parsedRConfList[h]'hlen)).contractEdges u a = true)
    (hav_ce : isContractEdge (configOfRConf (parsedRConfList[h]'hlen)).contractEdges a v = true)
    (hadj_uv : areAdjacentVertices H.dual (p.emb.rep u) (p.emb.rep v) darts.length = true) :
    False := by
  let c := configOfRConf (parsedRConfList[h]'hlen)
  have har : c.ringSize ≤ a := ceVert_deg_ge_two_is_int h hh hlen darts p huv hua_ce hav_ce
  obtain ⟨hun, han, hua_adj⟩ := isContractEdge_implies_adj_lt h hh hlen darts p hua_ce
  obtain ⟨_, hvn, hav_adj⟩ := isContractEdge_implies_adj_lt h hh hlen darts p hav_ce
  have hau_adj : c.adj a u = true := by rwa [p.adj_symm a u han hun]
  have hu_ce : u ∈ ceVerts c.contractEdges := (mem_ceVerts_of_isContractEdge hua_ce).1
  have ha_ce : a ∈ ceVerts c.contractEdges := (mem_ceVerts_of_isContractEdge hua_ce).2
  have hv_ce : v ∈ ceVerts c.contractEdges := (mem_ceVerts_of_isContractEdge hav_ce).2
  have hau_sv := vx_rep_distinct_in_dual h hh hlen darts h_mc p hmc ha_ce hu_ce han hun hua.symm
  have huv_sv := vx_rep_distinct_in_dual h hh hlen darts h_mc p hmc hu_ce hv_ce hun hvn huv
  have hva_sv := vx_rep_distinct_in_dual h hh hlen darts h_mc p hmc hv_ce ha_ce hvn han hav.symm
  have h1A := p.emb.dart_same_vertex_rep a har han u hun hau_adj
  have h1B : sameVertex H.dual (H.edge.f (p.emb.dart a u)) (p.emb.rep u) darts.length = true := by
    change sameVertex H.dual (H.dual.edge.f (p.emb.dart a u)) (p.emb.rep u) darts.length = true
    exact p.emb.dart_edge_same_vertex_rep a har han u hun hau_adj
  have h2A := p.emb.dart_same_vertex_rep a har han v hvn hav_adj
  have h2C : sameVertex H.dual (H.edge.f (p.emb.dart a v)) (p.emb.rep v) darts.length = true := by
    change sameVertex H.dual (H.dual.edge.f (p.emb.dart a v)) (p.emb.rep v) darts.length = true
    exact p.emb.dart_edge_same_vertex_rep a har han v hvn hav_adj
  have hstep := mc_three_cycle_consecutive darts h_mc p.emb.orient
    hau_sv huv_sv hva_sv h1A h1B h2A h2C hadj_uv
  have hc_uv : c.adj u v = true :=
    matchesConfCycle_adj_of_nodePerm_step h hh hlen darts p hmc har han hun hvn hau_adj hav_adj hstep
  have hreach : ContractReach c.contractEdges u v :=
    ContractReach.trans
      (ContractReach.step ((isContractPair_eq_isContractEdge c.contractEdges u a).symm ▸ hua_ce))
      (ContractReach.step ((isContractPair_eq_isContractEdge c.contractEdges a v).symm ▸ hav_ce))
  have hce_uv : isContractEdge c.contractEdges u v = true :=
    p.contract_no_shortcut u hun v hvn hreach hc_uv
  have hforest := rConf_forest_props h hh hlen
  have hno3 := hforest.2.1 u a v hua_ce hav_ce hua hav
  rw [isContractEdge_symm] at hce_uv
  rw [hce_uv] at hno3
  cases hno3

set_option linter.unusedVariables false in
private theorem subContractEdge_to_dart
    (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    {L_M : List H.Dart} {x y : Nat}
    (he : subContractEdge p.emb L_M x y) :
    ∃ d : H.Dart, SameOrbit H.face (p.emb.rep x) d ∧ SameOrbit H.face (p.emb.rep y) (H.edge.f d) := by
  let c := configOfRConf (parsedRConfList[h]'hlen)
  rcases he with ⟨_, _, _, _, q, hq_mem, _, hqp⟩
  obtain ⟨hqAr, hqAn, hqBn, hqAdj, _, _, hqor, hqd⟩ := contractEdgeDart_spec p hq_mem
  let qA := if c.ringSize ≤ q.1 then q.1 else q.2
  let qB := if c.ringSize ≤ q.1 then q.2 else q.1
  change contractEdgeDart p.emb q = p.emb.dart qA qB at hqd
  have hA := sameOrbit_face_of_sameVertex_dual darts h_mc
    (dual_sameVertex_symm darts h_mc (p.emb.dart_same_vertex_rep qA hqAr hqAn qB hqBn hqAdj))
  have hB : SameOrbit H.face (p.emb.rep qB) (H.edge.f (p.emb.dart qA qB)) :=
    sameOrbit_face_of_sameVertex_dual darts h_mc (dual_sameVertex_symm darts h_mc (by
      change sameVertex H.dual (H.dual.edge.f (p.emb.dart qA qB)) (p.emb.rep qB) darts.length = true
      exact p.emb.dart_edge_same_vertex_rep qA hqAr hqAn qB hqBn hqAdj))
  rcases hqp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hqor with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨p.emb.dart qA qB, ?_, ?_⟩
    · change qA = q.1 at h1; rw [← h1]; exact hA
    · change qB = q.2 at h2; rw [← h2]; exact hB
  · refine ⟨H.edge.f (p.emb.dart qA qB), ?_, ?_⟩
    · change qA = q.2 at h1; change qB = q.1 at h2; rw [← h2]; exact hB
    · change qA = q.2 at h1; rw [H.edge_edge, ← h1]; exact hA
  · refine ⟨H.edge.f (p.emb.dart qA qB), ?_, ?_⟩
    · change qB = q.2 at h2; rw [← h2]; exact hB
    · change qA = q.1 at h1; rw [H.edge_edge, ← h1]; exact hA
  · refine ⟨p.emb.dart qA qB, ?_, ?_⟩
    · change qA = q.2 at h1; rw [← h1]; exact hA
    · change qB = q.1 at h2; rw [← h2]; exact hB

/-- **Bridgelessness of the Contract-Deleted Subtype (`deleteEdgesSubtype`):**
    Contracting all edges in `mappedContractDarts p.emb` inside a minimal counterexample `H`
    never creates a bridge in `H'`. Any bridge `d'` in `H'` would give a path of length
    `L ∈ {0, 1, 2, 3}` in `ContractFaceEquiv`, ruled out by `mc_is_bridgeless` (`L=0`),
    `mc_dual_no_parallel` (`L=1`), `mc_dual_L2_adj_impossible` (`L=2`), and
    `mc_four_cycle_has_diag_edge_dual` + `mc_dual_L2_adj_impossible` (`L=3`). -/
theorem mc_contractDeleted_isBridgeless
    (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hmc : MatchesConfCycle (parsedRConfList[h]'hlen) H.dual darts p.emb)
    (h_free : ∀ d : H.Dart, H.edge.f d ≠ d := fun d => mc_edge_ne_self H darts h_mc d) :
    let rem : List H.Dart := contractSymDarts (T := H.dual) p.emb
    let H' := H.deleteEdgesSubtype rem (@contractSymDarts_edge_closed _ H.dual _ darts p.emb) h_free
    let darts' := subDarts darts rem
    H'.isBridgeless darts' darts'.length := by
  intro rem H' darts'
  have h_comp' : ∀ d' : H'.Dart, d' ∈ darts' := fun d' =>
    (mem_subDarts darts rem d').mpr (h_mc.complete d'.val)
  apply (isBridgeless_iff_no_sameOrbit_face_edge_jcs H' darts' h_comp').mpr
  intro d' h_same
  have hcfe_d : ContractFaceEquiv H (mappedContractDarts (T := H.dual) p.emb)
      d'.val (H'.edge.f d').val :=
    (deleteEdgesSubtype_sameOrbit_face_iff_contractFaceEquiv h hh hlen darts h_mc p hmc h_free
      d' (H'.edge.f d')).mp h_same
  rw [deleteEdgesSubtype_edge_val] at hcfe_d
  have hstate := contractFaceEquiv_to_simple_contract_path h hh hlen darts h_mc p hmc
    (fun _ hx => hx) hcfe_d
  rcases hstate with h_self | ⟨u, v, hun, hvn, hu_ce, hv_ce, hdu, hdv, hchain⟩
  · exact (isBridgeless_iff_no_sameOrbit_face_edge_jcs H darts h_mc.complete).mp
      h_mc.is_bridgeless d'.val h_self
  · have hd_sv_u := sameVertex_dual_of_sameOrbit_face darts h_mc hdu
    have hed_sv_v := sameVertex_dual_of_sameOrbit_face darts h_mc hdv
    have hadj_uv : areAdjacentVertices H.dual (p.emb.rep u) (p.emb.rep v) darts.length = true :=
      (areAdjacentVertices_iff H.dual darts h_mc.complete (Nat.le_refl _)
        (p.emb.rep u) (p.emb.rep v)).mpr ⟨d'.val,
          hd_sv_u,
          by simpa [Hypermap.dual] using hed_sv_v⟩
    cases hchain with
    | len1 huv hue =>
      rcases hue with ⟨_, _, _, _, q, hq_mem, hm_mem, hqp⟩
      let m := contractEdgeDart p.emb q
      obtain ⟨hqAr, hqAn, hqBn, hqAdj, _, _, hqor, hqd⟩ := contractEdgeDart_spec p hq_mem
      let c := configOfRConf (parsedRConfList[h]'hlen)
      let qA := if c.ringSize ≤ q.1 then q.1 else q.2
      let qB := if c.ringSize ≤ q.1 then q.2 else q.1
      change contractEdgeDart p.emb q = p.emb.dart qA qB at hqd
      have hmA : sameVertex H.dual m (p.emb.rep qA) darts.length = true := by
        dsimp [m]; rw [hqd]
        exact p.emb.dart_same_vertex_rep qA hqAr hqAn qB hqBn hqAdj
      have hmB : sameVertex H.dual (H.edge.f m) (p.emb.rep qB) darts.length = true := by
        dsimp [m]; rw [hqd]
        change sameVertex H.dual (H.dual.edge.f (p.emb.dart qA qB)) (p.emb.rep qB) darts.length = true
        exact p.emb.dart_edge_same_vertex_rep qA hqAr hqAn qB hqBn hqAdj
      have hAB_eq : (qA = u ∧ qB = v) ∨ (qA = v ∧ qB = u) := by
        rcases hqp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases hqor with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩
        · exact Or.inr ⟨h1, h2⟩
        · exact Or.inr ⟨h1, h2⟩
        · exact Or.inl ⟨h1, h2⟩
      rcases hAB_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hs1 : sameVertex H.dual d'.val m darts.length = true :=
          dual_sameVertex_trans darts h_mc hd_sv_u (dual_sameVertex_symm darts h_mc hmA)
        have hs2 : sameVertex H.dual (H.edge.f d'.val) (H.edge.f m) darts.length = true :=
          dual_sameVertex_trans darts h_mc hed_sv_v (dual_sameVertex_symm darts h_mc hmB)
        have hd_eq := mc_dual_no_parallel darts h_mc hs1 hs2
        have hm_rem : m ∈ rem := (mem_contractSymDarts_iff p.emb m).mpr ⟨m, hm_mem, Or.inl rfl⟩
        exact d'.property (hd_eq ▸ hm_rem)
      · have hs1 : sameVertex H.dual d'.val (H.edge.f m) darts.length = true :=
          dual_sameVertex_trans darts h_mc hd_sv_u (dual_sameVertex_symm darts h_mc hmB)
        have hs2 : sameVertex H.dual (H.edge.f d'.val) (H.edge.f (H.edge.f m)) darts.length = true := by
          rw [H.edge_edge]
          exact dual_sameVertex_trans darts h_mc hed_sv_v (dual_sameVertex_symm darts h_mc hmA)
        have hd_eq := mc_dual_no_parallel darts h_mc hs1 hs2
        have hm_rem : H.edge.f m ∈ rem :=
          (mem_contractSymDarts_iff p.emb (H.edge.f m)).mpr ⟨m, hm_mem, Or.inr rfl⟩
        exact d'.property (hd_eq ▸ hm_rem)
    | @len2 a _ hua hav huv hua_ce hav_ce =>
      exact mc_dual_L2_adj_impossible h hh hlen darts h_mc p hmc hua hav huv
        hua_ce.2.2.2.1 hav_ce.2.2.2.1 hadj_uv
    | @len3 a b _ hua hab hbv hub hav huv hua_ce hab_ce hbv_ce =>
      obtain ⟨d01, h01a, h01b⟩ := subContractEdge_to_dart h hh hlen darts h_mc p hua_ce
      obtain ⟨d12, h12a, h12b⟩ := subContractEdge_to_dart h hh hlen darts h_mc p hab_ce
      obtain ⟨d23, h23a, h23b⟩ := subContractEdge_to_dart h hh hlen darts h_mc p hbv_ce
      let rf : Fin 4 → H.Dart := fun i =>
        match i.val with
        | 0 => p.emb.rep u
        | 1 => p.emb.rep a
        | 2 => p.emb.rep b
        | _ => p.emb.rep v
      let cd : Fin 4 → H.Dart := fun i =>
        match i.val with
        | 0 => d01
        | 1 => d12
        | 2 => d23
        | _ => H.edge.f d'.val
      have han := hua_ce.2.1
      have hbn := hbv_ce.1
      have ha_ce := (subContractEdge_ceVerts hua_ce).2
      have hb_ce := (subContractEdge_ceVerts hbv_ce).1
      have h_diff : ∀ i j : Fin 4, i ≠ j → ¬ SameOrbit H.face (rf i) (rf j) := by
        intro i j hij hs
        have hsv := sameVertex_dual_of_sameOrbit_face darts h_mc hs
        have aux : ∀ (k1 k2 : Nat)
            (hk1c : k1 ∈ ceVerts (configOfRConf (parsedRConfList[h]'hlen)).contractEdges)
            (hk2c : k2 ∈ ceVerts (configOfRConf (parsedRConfList[h]'hlen)).contractEdges)
            (hk1n : k1 < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes)
            (hk2n : k2 < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes)
            (hne : k1 ≠ k2),
            sameVertex H.dual (p.emb.rep k1) (p.emb.rep k2) darts.length = true → False := by
          intro k1 k2 hk1c hk2c hk1n hk2n hne ht
          rw [vx_rep_distinct_in_dual h hh hlen darts h_mc p hmc hk1c hk2c hk1n hk2n hne] at ht
          cases ht
        rcases i with ⟨iv, hiv⟩; rcases j with ⟨jv, hjv⟩
        rcases (by omega : iv = 0 ∨ iv = 1 ∨ iv = 2 ∨ iv = 3) with rfl | rfl | rfl | rfl <;>
        rcases (by omega : jv = 0 ∨ jv = 1 ∨ jv = 2 ∨ jv = 3) with rfl | rfl | rfl | rfl <;>
        dsimp [rf] at hsv
        · exact hij rfl
        · exact aux u a hu_ce ha_ce hun han hua hsv
        · exact aux u b hu_ce hb_ce hun hbn hub hsv
        · exact aux u v hu_ce hv_ce hun hvn huv hsv
        · exact aux a u ha_ce hu_ce han hun hua.symm hsv
        · exact hij rfl
        · exact aux a b ha_ce hb_ce han hbn hab hsv
        · exact aux a v ha_ce hv_ce han hvn hav hsv
        · exact aux b u hb_ce hu_ce hbn hun hub.symm hsv
        · exact aux b a hb_ce ha_ce hbn han hab.symm hsv
        · exact hij rfl
        · exact aux b v hb_ce hv_ce hbn hvn hbv hsv
        · exact aux v u hv_ce hu_ce hvn hun huv.symm hsv
        · exact aux v a hv_ce ha_ce hvn han hav.symm hsv
        · exact aux v b hv_ce hb_ce hvn hbn hbv.symm hsv
        · exact hij rfl
      have h_a : ∀ i : Fin 4, SameOrbit H.face (rf i) (cd i) := by
        rintro ⟨iv, hiv⟩
        rcases (by omega : iv = 0 ∨ iv = 1 ∨ iv = 2 ∨ iv = 3) with rfl | rfl | rfl | rfl <;>
        dsimp [rf, cd]
        · exact h01a
        · exact h12a
        · exact h23a
        · exact sameOrbit_face_symm darts h_mc hdv
      have h_b : ∀ i : Fin 4,
          SameOrbit H.face (rf ⟨(i.val + 1) % 4, Nat.mod_lt _ (by omega)⟩) (H.edge.f (cd i)) := by
        rintro ⟨iv, hiv⟩
        rcases (by omega : iv = 0 ∨ iv = 1 ∨ iv = 2 ∨ iv = 3) with rfl | rfl | rfl | rfl <;>
        dsimp [rf, cd]
        · exact h01b
        · exact h12b
        · exact h23b
        · rw [H.edge_edge]; exact sameOrbit_face_symm darts h_mc hdu
      let cut : H.FaceCycleCut 4 :=
        { hk := by decide
          ringFace := rf
          cutDart := cd
          h_diff := h_diff
          h_a := h_a
          h_b := h_b
          h_disj_edge := faceCycleCut_disj_edge_of darts h_mc (by decide) rf cd h_diff h_a h_b }
      rcases mc_four_cycle_has_diag_edge_dual H darts h_mc cut with ⟨w, hwa, hwb⟩ | ⟨w, hwa, hwb⟩
      · have hadj_ub : areAdjacentVertices H.dual (p.emb.rep u) (p.emb.rep b) darts.length = true :=
          (areAdjacentVertices_iff H.dual darts h_mc.complete (Nat.le_refl _)
            (p.emb.rep u) (p.emb.rep b)).mpr ⟨w,
              sameVertex_dual_of_sameOrbit_face darts h_mc (sameOrbit_face_symm darts h_mc hwa),
              by simpa [Hypermap.dual] using
                sameVertex_dual_of_sameOrbit_face darts h_mc (sameOrbit_face_symm darts h_mc hwb)⟩
        exact mc_dual_L2_adj_impossible h hh hlen darts h_mc p hmc hua hab hub
          hua_ce.2.2.2.1 hab_ce.2.2.2.1 hadj_ub
      · have hadj_av : areAdjacentVertices H.dual (p.emb.rep a) (p.emb.rep v) darts.length = true :=
          (areAdjacentVertices_iff H.dual darts h_mc.complete (Nat.le_refl _)
            (p.emb.rep a) (p.emb.rep v)).mpr ⟨w,
              sameVertex_dual_of_sameOrbit_face darts h_mc (sameOrbit_face_symm darts h_mc hwa),
              by simpa [Hypermap.dual] using
                sameVertex_dual_of_sameOrbit_face darts h_mc (sameOrbit_face_symm darts h_mc hwb)⟩
        exact mc_dual_L2_adj_impossible h hh hlen darts h_mc p hmc hab hbv hav
          hab_ce.2.2.2.1 hbv_ce.2.2.2.1 hadj_av

/-- Every primal face orbit in a minimal counterexample `H` has size `≥ 5` (`mc_faceDegree_ge_five`),
    and at most one dart per contract edge (`|c.contractEdges| ≤ 4`) can hit it because
    distinct endpoints of a contract edge lie in distinct faces (`vx_rep_distinct_in_dual`).
    Hence every `H.face` orbit contains a surviving dart outside `contractSymDarts p.emb`. -/
theorem mc_faceOrbit_exists_not_mem_contractSym
    (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hmc : MatchesConfCycle (parsedRConfList[h]'hlen) H.dual darts p.emb)
    (z : H.Dart) :
    ∃ d : H.Dart, SameOrbit H.face z d ∧ d ∉ contractSymDarts (T := H.dual) p.emb := by
  let c := configOfRConf (parsedRConfList[h]'hlen)
  let rem : List H.Dart := contractSymDarts (T := H.dual) p.emb
  let orb := getOrbit H.face darts.length z
  exact Classical.byContradiction fun h_none => by
    have h_all_rem : ∀ d ∈ orb, d ∈ rem := fun d hd =>
      Classical.byContradiction fun hnot =>
        h_none ⟨d, (sameOrbit_iff_mem_getOrbit H.face darts h_mc.complete (Nat.le_refl _) z d).mpr hd, hnot⟩
    let pick : Nat × Nat → H.Dart := fun q =>
      if contractEdgeDart (T := H.dual) p.emb q ∈ orb then contractEdgeDart (T := H.dual) p.emb q
      else H.edge.f (contractEdgeDart (T := H.dual) p.emb q)
    have h_sub_map : ∀ d ∈ orb, d ∈ c.contractEdges.map pick := by
      intro d hd
      have hd_rem := h_all_rem d hd
      simp only [rem, mem_contractSymDarts_iff, mappedContractDarts, List.mem_map] at hd_rem
      rcases hd_rem with ⟨m, ⟨q, hq_mem, rfl⟩, rfl | rfl⟩
      · refine List.mem_map.mpr ⟨q, hq_mem, ?_⟩
        dsimp [pick]
        rw [if_pos hd]
      · refine List.mem_map.mpr ⟨q, hq_mem, ?_⟩
        dsimp [pick]
        by_cases hm_orb : contractEdgeDart (T := H.dual) p.emb q ∈ orb
        · exfalso
          have hso1 : SameOrbit H.face z (contractEdgeDart (T := H.dual) p.emb q) :=
            (sameOrbit_iff_mem_getOrbit H.face darts h_mc.complete (Nat.le_refl _) z _).mpr hm_orb
          have hso2 : SameOrbit H.face z (H.edge.f (contractEdgeDart (T := H.dual) p.emb q)) :=
            (sameOrbit_iff_mem_getOrbit H.face darts h_mc.complete (Nat.le_refl _) z _).mpr hd
          have hso_edge : SameOrbit H.face (contractEdgeDart (T := H.dual) p.emb q)
              (H.edge.f (contractEdgeDart (T := H.dual) p.emb q)) :=
            sameOrbit_trans H.face (sameOrbit_face_symm darts h_mc hso1) hso2
          obtain ⟨hqAr, hqAn, hqBn, hqAdj, hqAce, hqBce, _, hqd⟩ := contractEdgeDart_spec p hq_mem
          let qA := if c.ringSize ≤ q.1 then q.1 else q.2
          let qB := if c.ringSize ≤ q.1 then q.2 else q.1
          change contractEdgeDart (T := H.dual) p.emb q = p.emb.dart qA qB at hqd
          have hsv1 := p.emb.dart_same_vertex_rep qA hqAr hqAn qB hqBn hqAdj
          have hsv2 : sameVertex H.dual (H.edge.f (p.emb.dart qA qB)) (p.emb.rep qB) darts.length = true := by
            change sameVertex H.dual (H.dual.edge.f (p.emb.dart qA qB)) (p.emb.rep qB) darts.length = true
            exact p.emb.dart_edge_same_vertex_rep qA hqAr hqAn qB hqBn hqAdj
          have hsv_edge := sameVertex_dual_of_sameOrbit_face darts h_mc (hqd ▸ hso_edge)
          have hsv_AB := dual_sameVertex_trans darts h_mc (dual_sameVertex_symm darts h_mc hsv1)
            (dual_sameVertex_trans darts h_mc hsv_edge hsv2)
          have hirr := (ceNoDupUnordered_spec (rConf_forest_props h hh hlen).1).1
          have hqne : qA ≠ qB := by
            intro heq
            have hce : isContractEdge c.contractEdges qA qB = true := by
              simp only [isContractEdge, Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq,
                qA, qB]
              by_cases hr : c.ringSize ≤ q.1
              · simp [hr]; left; simpa [c] using hq_mem
              · simp [hr]; right; simpa [c] using hq_mem
            rw [heq] at hce
            have hbad := hirr qB
            rw [hce] at hbad; cases hbad
          rw [vx_rep_distinct_in_dual h hh hlen darts h_mc p hmc hqAce hqBce hqAn hqBn hqne] at hsv_AB
          cases hsv_AB
        · rw [if_neg hm_orb]; rfl
    have h5 : 5 ≤ orb.length := mc_faceDegree_ge_five H darts h_mc z
    have hnd_orb : orb.Nodup := getOrbit_nodup H.face darts.length z
    have hle_map : orb.length ≤ (c.contractEdges.map pick).length :=
      nodup_length_le_of_subset orb (c.contractEdges.map pick) hnd_orb h_sub_map
    have hle4 : c.contractEdges.length ≤ 4 := Math.Unavoidability.contract_edges_le_four h hh
    rw [List.length_map] at hle_map
    omega

/-- Lifting a proper `H'.FaceColoring` of the contract-deleted subtype hypermap `H'`
    to a quotient coloring `VertexColoringMod H.dual (mappedContractDarts p.emb)`. -/
noncomputable def liftContractDeletedColoring
    (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    {H : Hypermap} [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts)
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hmc : MatchesConfCycle (parsedRConfList[h]'hlen) H.dual darts p.emb)
    (h_free : ∀ d : H.Dart, H.edge.f d ≠ d := fun d => mc_edge_ne_self H darts h_mc d)
    (fc' : (H.deleteEdgesSubtype (contractSymDarts (T := H.dual) p.emb)
      (@contractSymDarts_edge_closed _ H.dual _ darts p.emb) h_free).FaceColoring) :
    VertexColoringMod H.dual (mappedContractDarts (T := H.dual) p.emb) :=
  let rem : List H.Dart := contractSymDarts (T := H.dual) p.emb
  let M : List H.Dart := mappedContractDarts (T := H.dual) p.emb
  let H' := H.deleteEdgesSubtype rem (@contractSymDarts_edge_closed _ H.dual _ darts p.emb) h_free
  let repDart : H.Dart → H'.Dart := fun z =>
    let ex := mc_faceOrbit_exists_not_mem_contractSym h hh hlen darts h_mc p hmc z
    ⟨Classical.choose ex, (Classical.choose_spec ex).2⟩
  let col : H.Dart → Color := fun z => fc'.color (repDart z)
  have fc_orb : ∀ {a b : H'.Dart}, SameOrbit H'.face a b → fc'.color a = fc'.color b := by
    rintro a b ⟨k, rfl⟩
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [Perm.iter_succ, fc'.face_invariant]
      exact ih
  have col_cfe : ∀ {x y : H.Dart}, ContractFaceEquiv H M x y → col x = col y := by
    intro x y hxy
    have hx_so : SameOrbit H.face x (repDart x).val :=
      (Classical.choose_spec (mc_faceOrbit_exists_not_mem_contractSym h hh hlen darts h_mc p hmc x)).1
    have hy_so : SameOrbit H.face y (repDart y).val :=
      (Classical.choose_spec (mc_faceOrbit_exists_not_mem_contractSym h hh hlen darts h_mc p hmc y)).1
    have hcfe : ContractFaceEquiv H M (repDart x).val (repDart y).val :=
      ContractFaceEquiv.trans
        (ContractFaceEquiv.face (sameOrbit_face_symm darts h_mc hx_so))
        (ContractFaceEquiv.trans hxy (ContractFaceEquiv.face hy_so))
    have hso' : SameOrbit H'.face (repDart x) (repDart y) :=
      (deleteEdgesSubtype_sameOrbit_face_iff_contractFaceEquiv h hh hlen darts h_mc p hmc h_free
        (repDart x) (repDart y)).mpr hcfe
    exact fc_orb hso'
  have col_nrem : ∀ (z : H.Dart) (hz : z ∉ rem), col z = fc'.color ⟨z, hz⟩ := by
    intro z hz
    have hz_so : SameOrbit H.face z (repDart z).val :=
      (Classical.choose_spec (mc_faceOrbit_exists_not_mem_contractSym h hh hlen darts h_mc p hmc z)).1
    have hso' : SameOrbit H'.face ⟨z, hz⟩ (repDart z) :=
      (deleteEdgesSubtype_sameOrbit_face_iff_contractFaceEquiv h hh hlen darts h_mc p hmc h_free
        ⟨z, hz⟩ (repDart z)).mpr (ContractFaceEquiv.face hz_so)
    exact (fc_orb hso').symm
  { color := col
    node_invariant := fun d => by
      have hso : SameOrbit H.face (H.dual.node.f d) d :=
        ⟨1, by change H.face.f (H.face.inv d) = d; exact H.face.right_inv d⟩
      exact col_cfe (ContractFaceEquiv.face hso)
    contract_same := fun d hd => by
      exact (col_cfe (ContractFaceEquiv.edge hd)).symm
    edge_proper := fun d hd1 hd2 => by
      have hd_nrem : d ∉ rem := by
        intro hmem
        simp only [rem, mem_contractSymDarts_iff] at hmem
        rcases hmem with ⟨m, hm, rfl | rfl⟩
        · exact hd1 hm
        · change H.dual.edge.f (H.dual.edge.f m) ∉ M at hd2
          rw [H.dual.edge_edge] at hd2
          exact hd2 hm
      have hed_nrem : H.edge.f d ∉ rem :=
        fun hmem => hd_nrem ((contractSymDarts_edge_closed p.emb d).mpr hmem)
      rw [col_nrem (H.edge.f d) hed_nrem, col_nrem d hd_nrem]
      have h_edge_val : H'.edge.f ⟨d, hd_nrem⟩ = ⟨H.edge.f d, hed_nrem⟩ :=
        Subtype.ext (deleteEdgesSubtype_edge_val H rem _ h_free ⟨d, hd_nrem⟩)
      rw [← h_edge_val]
      exact fc'.edge_proper ⟨d, hd_nrem⟩ }

/-- **Existence of Contracted Quotient Coloring (`VertexColoringMod`) for Any Matched C-Reducible
    Configuration:** In any planar, bridgeless minimal counterexample `H`, every matched C-reducible
    configuration `rc = parsedRConfList[h]` (`h < 633`, `rc.contractEdges ≠ []`) admits
    a valid `VertexColoringMod H.dual (mappedContractDarts p.emb)`. -/
theorem mc_c_reducible_mod_coloring
    (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    (H : Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_mc : H.PrimalMinimalCounterexample darts)
    (hC : (configOfRConf (parsedRConfList[h]'hlen)).contractEdges ≠ [])
    (p : CorrespondingProjection (configOfRConf (parsedRConfList[h]'hlen)) H.dual darts)
    (hmc : MatchesConfCycle (parsedRConfList[h]'hlen) H.dual darts p.emb) :
    Nonempty (VertexColoringMod H.dual (mappedContractDarts (T := H.dual) p.emb)) := by
  let c := configOfRConf (parsedRConfList[h]'hlen)
  let rem : List H.Dart := contractSymDarts (T := H.dual) p.emb
  let h_free : ∀ d : H.Dart, H.edge.f d ≠ d := fun d => mc_edge_ne_self H darts h_mc d
  let H' := H.deleteEdgesSubtype rem (@contractSymDarts_edge_closed _ H.dual _ darts p.emb) h_free
  let darts' := subDarts darts rem
  have h_comp' : ∀ x : H'.Dart, x ∈ darts' := fun x =>
    (mem_subDarts darts rem x).mpr (h_mc.complete x.val)
  have h_surv : ∃ d ∈ darts, d ∉ rem := by
    have ⟨d0, _⟩ := List.exists_mem_of_ne_nil darts h_mc.nonempty
    obtain ⟨d, _, hd_nrem⟩ := mc_faceOrbit_exists_not_mem_contractSym h hh hlen darts h_mc p hmc d0
    exact ⟨d, h_mc.complete d, hd_nrem⟩
  have h_complete' : darts'.Nodup ∧ (∀ x : H'.Dart, x ∈ darts') ∧ darts' ≠ [] :=
    ⟨subDarts_nodup darts rem h_mc.nodup, h_comp', subDarts_nonempty darts rem h_surv⟩
  have h_rem : ∃ r ∈ darts, r ∈ rem := by
    obtain ⟨q, hq_mem⟩ := List.exists_mem_of_ne_nil c.contractEdges hC
    let m := contractEdgeDart (T := H.dual) p.emb q
    have hm_M : m ∈ mappedContractDarts (T := H.dual) p.emb :=
      List.mem_map.mpr ⟨q, hq_mem, rfl⟩
    have hm_rem : m ∈ rem := (mem_contractSymDarts_iff p.emb m).mpr ⟨m, hm_M, Or.inl rfl⟩
    exact ⟨m, h_mc.complete m, hm_rem⟩
  have h_lt : darts'.length < darts.length :=
    exciseSubtype_strictly_smaller darts rem h_rem
  have h_planar' : H'.isPlanar darts'.length darts' = true :=
    deleteEdgesSubtype_isPlanar H darts rem (@contractSymDarts_edge_closed _ H.dual _ darts p.emb)
      h_free h_mc.nodup h_mc.complete (Nat.le_refl _) h_mc.is_planar
      darts' h_complete'.1 h_comp' (Nat.le_refl _)
  have h_bridge' : H'.isBridgeless darts' darts'.length :=
    mc_contractDeleted_isBridgeless h hh hlen darts h_mc p hmc h_free
  obtain ⟨fc'⟩ := h_mc.is_minimal H' darts' h_complete'.1 h_comp' h_complete'.2.2 h_lt h_planar' h_bridge'
  exact ⟨liftContractDeletedColoring h hh hlen darts h_mc p hmc h_free fc'⟩

end ContractDeletedColoring

end Hypermap
