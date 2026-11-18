module

/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
Released under Apache 2.0 license.
-/
public import FourColorTheorem.Math.Unavoidability.ConfGeomCertBase
public import FourColorTheorem.Math.Unavoidability.ConfGeomCertBlk0
public import FourColorTheorem.Math.Unavoidability.ConfGeomCertBlk1
public import FourColorTheorem.Math.Unavoidability.ConfGeomCertBlk2
public import FourColorTheorem.Math.Unavoidability.ConfGeomCertBlk3
public import FourColorTheorem.Math.Unavoidability.ConfGeomCertBlk4

@[expose] public section

/-!
# Certified Configuration Geometric & Combinatorial Invariants (Stage R.1)

This frozen leaf aggregator combines `ConfGeomCertBlk0`..`ConfGeomCertBlk4` into universal
certified theorems across all 633 unavoidable configurations (`0 ≤ h < 633`):
1. `fastConf_geom_int_runs`: Cyclic interior-neighbor run structure around every interior vertex,
   including explicit `QStep` pinning for every `runs = 2` gap.
2. `fastConf_geom_qSteps`: `QStep` target distinctness (`Nodup`), complete interior coverage,
   and face consistency in `iv.cyc`.
3. `fastConf_geom_halfEdge_recip`: Half-edge reciprocity across `iv.cyc`.
4. `fastConf_geom_cyc_ring_pairs`: Two-ring cyclic pair orientation and fan-head alignment.
5. `fastConf_geom_ring_fans`: Ring-vertex fan consistency across consecutive ring neighbors.
6. `fastConf_geom_tri_clique_in_cyc`: Absence of non-facial triangles.
7. `fastConf_geom_triad4`: RSST `(3.6)` `|X| = 4` triad witness in `[r .. n - 1]`.
-/

namespace Math.Unavoidability

open Math Math.Discharging Math.FastReducer GeomCert

private theorem row_check_geom_table (b r : Nat) (hb : b < 10) (hr : r < 8)
    (hb0 : b < Discharging.fastConfTable.length)
    (hb1 : r < (Discharging.fastConfTable[b]'hb0).length)
    (rb0 : b < rcTable.length)
    (rb1 : r < (rcTable[b]'rb0).length) :
    checkListZipGeom ((Discharging.fastConfTable[b]'hb0)[r]'hb1) ((rcTable[b]'rb0)[r]'rb1) = true := by
  match b with
  | 0 => exact geom_blk_0 r hr
  | 1 => exact geom_blk_1 r hr
  | 2 => exact geom_blk_2 r hr
  | 3 => exact geom_blk_3 r hr
  | 4 => exact geom_blk_4 r hr
  | 5 => exact geom_blk_5 r hr
  | 6 => exact geom_blk_6 r hr
  | 7 => exact geom_blk_7 r hr
  | 8 => exact geom_blk_8 r hr
  | 9 => exact geom_blk_9 r hr
  | _ + 10 => omega

/-- Universal geometric certificate: `checkPairGeom` holds for every configuration index `h < 633`. -/
theorem fastConf_geom_all (h : Nat) (hh : h < 633) :
    checkPairGeom (Discharging.lookupFastConfRec h)
      (parsedRConfList[h]'(parsedRConfList_length ▸ hh)) = true := by
  obtain ⟨hb0, hb1, hb2, hfc⟩ := lookupFastConfRec_eq_table h hh
  obtain ⟨rb0, rb1, rb2, hrc⟩ := parsedRConfList_eq_table h hh
  rw [hfc, hrc]
  have h0 : h >>> 6 < 10 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have h1 : (h >>> 3) &&& 7 < 8 := by
    rw [show (7 : Nat) = 2 ^ 3 - 1 from rfl, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by decide)
  have hblk := row_check_geom_table (h >>> 6) ((h >>> 3) &&& 7) h0 h1 hb0 hb1 rb0 rb1
  exact checkListZipGeom_getElem _ _ hblk (h &&& 7) hb2 rb2

/-- Certified `IntRunShape` around every interior vertex of every unavoidable configuration. -/
theorem fastConf_geom_int_runs (h : Nat) (hh : h < 633)
    (iu : Nat) (hiu : iu < (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).interiorSize) :
    let rc := parsedRConfList[h]'(parsedRConfList_length ▸ hh)
    let fc := lookupFastConfRec h
    let c := configOfRConf rc
    have hiu' : iu < fc.intVerts.length := by
      rw [(fastConf_equiv_header h hh).2.2.2.2.2.2.2.2.2.2.1]; exact hiu
    have hu0 : c.ringSize + iu < rc.adj.size := by
      have hiu_c : iu < c.interiorSize := hiu
      have hsz : rc.adj.size = c.totalNodes := (fastConf_equiv_header h hh).2.2.2.2.2.2.2.2.2.2.2.1
      have htot : c.totalNodes = c.ringSize + c.interiorSize := rfl
      omega
    let iv := fc.intVerts[iu]'hiu'
    let nbrs := (rc.adj[c.ringSize + iu]'hu0).toList
    ∃ k < nbrs.length, IntRunShape rc.r c fc iv (nbrs.drop k ++ nbrs.take k) :=
  geom_int_runs_of h hh (fastConf_geom_all h hh) iu hiu

/-- Certified `QStep` distinctness, coverage, and facial consistency across all 633 configurations. -/
theorem fastConf_geom_qSteps (h : Nat) (hh : h < 633) :
    let rc := parsedRConfList[h]'(parsedRConfList_length ▸ hh)
    let fc := lookupFastConfRec h
    let cov := fc.z0 :: fc.z1 :: fc.qSteps.map (·.z)
    cov.Nodup ∧
    (∀ iv ∈ fc.intVerts, iv.u ∈ cov) ∧
    (∀ q ∈ fc.qSteps,
      (rc.r < q.v → ∃ iv ∈ fc.intVerts, iv.u = q.v ∧ { v := q.z, w := q.u : CycPair } ∈ iv.cyc) ∧
      (q.v ≤ rc.r → rc.r < q.u ∧ ∃ iv ∈ fc.intVerts, iv.u = q.u ∧ { v := q.v, w := q.z : CycPair } ∈ iv.cyc)) :=
  geom_qSteps_of h hh (fastConf_geom_all h hh)

/-- Certified half-edge reciprocity across all 633 configurations. -/
theorem fastConf_geom_halfEdge_recip (h : Nat) (hh : h < 633) :
    let rc := parsedRConfList[h]'(parsedRConfList_length ▸ hh)
    let fc := lookupFastConfRec h
    ∀ iv ∈ fc.intVerts, ∀ cp ∈ iv.cyc,
      (rc.r < cp.v → ∃ iv2 ∈ fc.intVerts, iv2.u = cp.v ∧ { v := cp.w, w := iv.u : CycPair } ∈ iv2.cyc) ∧
      (rc.r < cp.w → ∃ iv2 ∈ fc.intVerts, iv2.u = cp.w ∧ { v := iv.u, w := cp.v : CycPair } ∈ iv2.cyc) :=
  geom_halfEdge_recip_of h hh (fastConf_geom_all h hh)

/-- Certified two-ring cyclic pair orientation and fan-head alignment across all 633 configurations. -/
theorem fastConf_geom_cyc_ring_pairs (h : Nat) (hh : h < 633) :
    let rc := parsedRConfList[h]'(parsedRConfList_length ▸ hh)
    let fc := lookupFastConfRec h
    ∀ iv ∈ fc.intVerts, ∀ cp ∈ iv.cyc,
      cp.v ≤ rc.r → cp.w ≤ rc.r →
        cp.w - 1 = (cp.v - 1 + 1) % rc.r ∧
        ∃ hx : cp.v - 1 < rc.adj.size,
          ((rc.adj[cp.v - 1]'hx).toList.drop 1).dropLast.head? = some (iv.u - 1) :=
  geom_cyc_ring_pairs_of h hh (fastConf_geom_all h hh)

/-- Certified ring fan consistency across all 633 configurations. -/
theorem fastConf_geom_ring_fans (h : Nat) (hh : h < 633)
    (x : Nat) (hx : x < (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).r) :
    let rc := parsedRConfList[h]'(parsedRConfList_length ▸ hh)
    let fc := lookupFastConfRec h
    let nextR := (x + 1) % rc.r
    let prevR := (x + rc.r - 1) % rc.r
    have hxn : x < rc.adj.size := by
      have hx_rc : x < rc.r := hx
      have hsz : rc.adj.size = (configOfRConf rc).totalNodes := (fastConf_equiv_header h hh).2.2.2.2.2.2.2.2.2.2.2.1
      have hr : (configOfRConf rc).ringSize = rc.r := (fastConf_equiv_header h hh).2.2.1
      have htot : (configOfRConf rc).totalNodes = (configOfRConf rc).ringSize + (configOfRConf rc).interiorSize := rfl
      omega
    have hnextn : nextR < rc.adj.size := by
      have hsz : rc.adj.size = (configOfRConf rc).totalNodes := (fastConf_equiv_header h hh).2.2.2.2.2.2.2.2.2.2.2.1
      have hr : (configOfRConf rc).ringSize = rc.r := (fastConf_equiv_header h hh).2.2.1
      have hr6 : 6 ≤ (configOfRConf rc).ringSize := (fastConf_equiv_header h hh).2.2.2.2.2.1
      have htot : (configOfRConf rc).totalNodes = (configOfRConf rc).ringSize + (configOfRConf rc).interiorSize := rfl
      have : nextR < rc.r := Nat.mod_lt _ (by omega)
      omega
    let fans := ((rc.adj[x]'hxn).toList.drop 1).dropLast
    let nextFans := ((rc.adj[nextR]'hnextn).toList.drop 1).dropLast
    fans ≠ [] ∧
    nextFans.getLast? = fans.head? ∧
    (∀ u1, fans.head? = some u1 →
      ∃ iv1 ∈ fc.intVerts, iv1.u = u1 + 1 ∧ { v := x + 1, w := nextR + 1 : CycPair } ∈ iv1.cyc) ∧
    (∀ um, fans.getLast? = some um →
      ∃ ivm ∈ fc.intVerts, ivm.u = um + 1 ∧ { v := prevR + 1, w := x + 1 : CycPair } ∈ ivm.cyc) ∧
    (∀ k (hk : k + 1 < fans.length),
      ∃ ivk ∈ fc.intVerts, ∃ ivk1 ∈ fc.intVerts,
        ivk.u = fans[k]'(Nat.lt_of_succ_lt hk) + 1 ∧
        ivk1.u = fans[k + 1]'hk + 1 ∧
        { v := fans[k + 1]'hk + 1, w := x + 1 : CycPair } ∈ ivk.cyc ∧
        { v := x + 1, w := fans[k]'(Nat.lt_of_succ_lt hk) + 1 : CycPair } ∈ ivk1.cyc) :=
  geom_ring_fans_of h hh (fastConf_geom_all h hh) x hx

/-- Certified absence of non-facial triangles across all 633 configurations. -/
theorem fastConf_geom_tri_clique_in_cyc (h : Nat) (hh : h < 633)
    {a b d : Nat}
    (ha : a < (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).n)
    (hb : b < (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).n)
    (hd : d < (parsedRConfList[h]'(parsedRConfList_length ▸ hh)).n)
    (hab : (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).adj a b = true)
    (hbd : (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).adj b d = true)
    (had : (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).adj a d = true) :
    ∃ iv ∈ (lookupFastConfRec h).intVerts,
      (iv.u = a + 1 ∧ ({ v := b + 1, w := d + 1 : CycPair } ∈ iv.cyc ∨ { v := d + 1, w := b + 1 : CycPair } ∈ iv.cyc)) ∨
      (iv.u = b + 1 ∧ ({ v := a + 1, w := d + 1 : CycPair } ∈ iv.cyc ∨ { v := d + 1, w := a + 1 : CycPair } ∈ iv.cyc)) ∨
      (iv.u = d + 1 ∧ ({ v := a + 1, w := b + 1 : CycPair } ∈ iv.cyc ∨ { v := b + 1, w := a + 1 : CycPair } ∈ iv.cyc)) :=
  geom_tri_clique_in_cyc_of h hh (fastConf_geom_all h hh) ha hb hd hab hbd had

/-- Certified RSST `(3.6)` `|X| = 4` triad witness across all `|X| = 4` configurations. -/
theorem fastConf_geom_triad4 (h : Nat) (hh : h < 633)
    (hce : (configOfRConf (parsedRConfList[h]'(parsedRConfList_length ▸ hh))).contractEdges.length = 4) :
    let rc := parsedRConfList[h]'(parsedRConfList_length ▸ hh)
    let c := configOfRConf rc
    ∃ v_tri : Nat, ∃ hv : v_tri < rc.adj.size,
      rc.r ≤ v_tri ∧ v_tri < rc.n ∧
      3 ≤ ((rc.adj[v_tri]'hv).toList.filter
        (fun w => decide (∃ p ∈ c.contractEdges, w = p.1 ∨ w = p.2) && !isContractPair c.contractEdges v_tri w)).length :=
  geom_triad4_of h hh (fastConf_geom_all h hh) hce

end Math.Unavoidability
