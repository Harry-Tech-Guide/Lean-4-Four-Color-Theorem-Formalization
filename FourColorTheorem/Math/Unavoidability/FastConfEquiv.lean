/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
Released under Apache 2.0 license.
-/
import FourColorTheorem.Math.Unavoidability.FastConfEquivBase
import FourColorTheorem.Math.Unavoidability.FastConfEquivData
import FourColorTheorem.Math.Unavoidability.FastConfEquivBlk0
import FourColorTheorem.Math.Unavoidability.FastConfEquivBlk1
import FourColorTheorem.Math.Unavoidability.FastConfEquivBlk2
import FourColorTheorem.Math.Unavoidability.FastConfEquivBlk3
import FourColorTheorem.Math.Unavoidability.FastConfEquivBlk4
import FourColorTheorem.Math.Unavoidability.FastConfEquivBlk5
import FourColorTheorem.Math.Unavoidability.FastConfEquivBlk6
import FourColorTheorem.Math.Unavoidability.FastConfEquivBlk7
import FourColorTheorem.Math.Unavoidability.FastConfEquivBlk8
import FourColorTheorem.Math.Unavoidability.FastConfEquivBlk9

/-!
# Stage P.3: 633-Configuration `FastConf` ↔ `RConf` Equivalence & Contract Safety

This module assembles the 10 pre-built block certificate modules
(`FastConfEquivBlk0`..`FastConfEquivBlk9`) into universal structural equivalence
and contract-safety theorems across all 633 unavoidable configurations (`0 ≤ h < 633`)
between `Math.Discharging.lookupFastConfRec h` and `Math.parsedRConfList[h]` /
`Math.theUnavoidableSet[h]` (`configOfRConf rc`):

1. `fastConf_equiv_header`: Header dimensions, bounds (`6 ≤ r ≤ 14`, `4 ≤ intN ≤ 12`,
   `n ≤ 26`), and `z0/z1` roots.
2. `fastConf_equiv_adj`: Full symmetry, nodup neighbor lists, `c.adj ↔ rc.adj`,
   and `fc.adjMat` bit-matrix equivalence.
3. `fastConf_equiv_ring_and_fans`: Ring cycle, zero ring chords, and canonical
   ring-to-interior fans.
4. `fastConf_equiv_intVerts`: Interior vertices `fc.intVerts` degrees `5..11`,
   `d ≤ 8 ∨ u = fc.z0`, `≥ 2` interior neighbors, and exact cyclic triangles `iv.cyc`.
5. `fastConf_equiv_qSteps`: `fc.z0 :: fc.z1 :: qSteps.map (·.z)` interior coverage
   without duplicates and valid triangles.
6. `fastConf_equiv_contract_safe`: RSST `(3.6)` contract safety (`0` ring-ring contracts,
   `≤ 1` contract per ring vertex and per triangle, no contract-component shortcut edge).
-/

namespace Math.Unavoidability

open Math Math.Discharging Internal

private theorem row_check_table (b r : Nat) (hb : b < 10) (hr : r < 8)
    (hb0 : b < Discharging.fastConfTable.length)
    (hb1 : r < (Discharging.fastConfTable[b]'hb0).length)
    (rb0 : b < rcTable.length)
    (rb1 : r < (rcTable[b]'rb0).length) :
    checkListZipPrefix ((Discharging.fastConfTable[b]'hb0)[r]'hb1) ((rcTable[b]'rb0)[r]'rb1) = true := by
  match b with
  | 0 => exact equiv_blk_0 r hr
  | 1 => exact equiv_blk_1 r hr
  | 2 => exact equiv_blk_2 r hr
  | 3 => exact equiv_blk_3 r hr
  | 4 => exact equiv_blk_4 r hr
  | 5 => exact equiv_blk_5 r hr
  | 6 => exact equiv_blk_6 r hr
  | 7 => exact equiv_blk_7 r hr
  | 8 => exact equiv_blk_8 r hr
  | 9 => exact equiv_blk_9 r hr
  | _ + 10 => omega

/-- Universal certificate theorem: `checkConfEquiv` holds for every index `h < 633`. -/
theorem fastConf_equiv_all (h : Nat) (hh : h < 633) :
    checkConfEquiv (Discharging.lookupFastConfRec h)
      (parsedRConfList[h]'(by rw [parsedRConfList_length]; exact hh)) = true := by
  obtain ⟨hb0, hb1, hb2, hfc⟩ := lookupFastConfRec_eq_table h hh
  obtain ⟨rb0, rb1, rb2, hrc⟩ := parsedRConfList_eq_table h hh
  rw [hfc, hrc]
  obtain ⟨h0, h1, _, _, _, _⟩ := bit_chunk_arith h hh
  have hblk := row_check_table (h >>> 6) ((h >>> 3) &&& 7) h0 h1 hb0 hb1 rb0 rb1
  have hlen :
      ((rcTable[h >>> 6]'rb0)[(h >>> 3) &&& 7]'rb1).length ≤
      ((Discharging.fastConfTable[h >>> 6]'hb0)[(h >>> 3) &&& 7]'hb1).length := by
    rw [fcTable_cell_len (h >>> 6) ((h >>> 3) &&& 7) h0 h1,
      rcTable_cell_len (h >>> 6) ((h >>> 3) &&& 7) h0 h1]
    by_cases h9 : h >>> 6 < 9
    · simp [h9]
    · by_cases h7 : (h >>> 3) &&& 7 < 7
      · simp [h9, h7]
      · simp [h9, h7]
  exact checkListZipPrefix_spec _ _ hblk hlen (h &&& 7) rb2

/-- **Theorem 1:** Header dimensions, bounds, and `z0/z1` roots match across all 633 configurations. -/
theorem fastConf_equiv_header (h : Nat) (hh : h < 633) :
    let fc := Discharging.lookupFastConfRec h
    let rc := parsedRConfList[h]'(by rw [parsedRConfList_length]; exact hh)
    let c := configOfRConf rc
    fc.ring = c.ringSize ∧
    fc.nverts = c.totalNodes ∧
    c.ringSize = rc.r ∧
    c.interiorSize = rc.n - rc.r ∧
    c.totalNodes = rc.n ∧
    6 ≤ c.ringSize ∧ c.ringSize ≤ 14 ∧
    4 ≤ c.interiorSize ∧ c.interiorSize ≤ 12 ∧
    c.totalNodes ≤ 26 ∧
    fc.intVerts.length = c.interiorSize ∧
    rc.adj.size = c.totalNodes ∧
    rc.earlier.size = c.totalNodes ∧
    fc.ring < fc.z0 ∧ fc.z0 ≤ fc.nverts ∧
    fc.ring < fc.z1 ∧ fc.z1 ≤ fc.nverts ∧
    fc.z0 ≠ fc.z1 ∧
    c.adj (fc.z0 - 1) (fc.z1 - 1) = true := by
  intro fc rc c
  have h_all : checkConfEquiv fc rc = true := fastConf_equiv_all h hh
  obtain ⟨u⟩ := unpackCheckConfEquiv h_all
  have hhdr := u.h_hdr
  dsimp [checkHeaderEquiv] at hhdr
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hhdr
  rcases hhdr with ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hring, hn⟩, hrle⟩, hr6⟩, hr14⟩, hi4⟩, hi12⟩, hn26⟩, hadjLen⟩, hearLen⟩, hivLen⟩
  have hcr : c.ringSize = rc.r := rfl
  have hci : c.interiorSize = rc.n - rc.r := rfl
  have htot : c.totalNodes = rc.n := by
    dsimp [c, configOfRConf, Configuration.totalNodes]; omega
  have hqs := u.h_qs
  dsimp [checkQStepEquiv] at hqs
  simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, testBit_and_one_eq] at hqs
  rcases hqs with ⟨⟨⟨⟨⟨⟨⟨hz0_gt, hz0_le⟩, hz1_gt⟩, hz1_le⟩, hzne⟩, hz_adj⟩, _⟩, _⟩
  obtain ⟨_, _, _, hadjSpec, hcadj⟩ := adj_eq_of_unpacked u
  have hadj_z01 : c.adj (fc.z0 - 1) (fc.z1 - 1) = true := by
    have hz0lt : fc.z0 - 1 < rc.n := by omega
    have hz1lt : fc.z1 - 1 < rc.n := by omega
    rw [hcadj (fc.z0 - 1) hz0lt (fc.z1 - 1) hz1lt]
    rw [← (hadjSpec (fc.z0 - 1) hz0lt).2.2 (fc.z1 - 1)]
    exact hz_adj
  have hadj_sz : rc.adj.size = c.totalNodes := by
    have : rc.adj.size = (rc.adj.toList.map Array.toList).length := by simp
    omega
  have hear_sz : rc.earlier.size = c.totalNodes := by
    have : rc.earlier.size = (rc.earlier.toList.map Array.toList).length := by simp
    omega
  exact ⟨hring, by rw [hn, htot], hcr, hci, htot,
    by omega, by omega, by omega, by omega, by omega,
    hivLen, hadj_sz, hear_sz, by omega, by omega, by omega, by omega, hzne, hadj_z01⟩

/-- **Theorem 2:** Symmetry, nodup neighbor lists, `c.adj ↔ rc.adj`, and `fc.adjMat` bit-matrix equivalence. -/
theorem fastConf_equiv_adj (h : Nat) (hh : h < 633) :
    let fc := Discharging.lookupFastConfRec h
    let rc := parsedRConfList[h]'(by rw [parsedRConfList_length]; exact hh)
    let c := configOfRConf rc
    (∀ x (hx : x < c.totalNodes),
      (rc.adj[x]'(by
        have hsz : rc.adj.size = c.totalNodes := (fastConf_equiv_header h hh).2.2.2.2.2.2.2.2.2.2.2.1
        omega)).toList.Nodup ∧
      ∀ v ∈ (rc.adj[x]'(by
        have hsz : rc.adj.size = c.totalNodes := (fastConf_equiv_header h hh).2.2.2.2.2.2.2.2.2.2.2.1
        omega)).toList, v < c.totalNodes ∧ v ≠ x) ∧
    (∀ x (hx : x < c.totalNodes), ∀ y < c.totalNodes,
      c.adj x y = (rc.adj[x]'(by
        have hsz : rc.adj.size = c.totalNodes := (fastConf_equiv_header h hh).2.2.2.2.2.2.2.2.2.2.2.1
        omega)).toList.contains y) ∧
    (∀ x < c.totalNodes, ∀ y < c.totalNodes,
      c.adj x y = c.adj y x ∧ c.adj x x = false) ∧
    (∀ iu < c.interiorSize, ∀ iv < c.interiorSize,
      fc.adjMat.testBit (iu * 12 + iv) = c.adj (c.ringSize + iu) (c.ringSize + iv)) := by
  intro fc rc c
  have h_all : checkConfEquiv fc rc = true := fastConf_equiv_all h hh
  obtain ⟨u⟩ := unpackCheckConfEquiv h_all
  obtain ⟨hadjL, _, _, hadjSpec, hcadj⟩ := adj_eq_of_unpacked u
  have htot : c.totalNodes = rc.n := (fastConf_equiv_header h hh).2.2.2.2.1
  have hadj_sz : rc.adj.size = c.totalNodes := (fastConf_equiv_header h hh).2.2.2.2.2.2.2.2.2.2.2.1
  have hstr := u.h_str
  dsimp [checkStructureEquiv] at hstr
  simp only [Bool.and_eq_true] at hstr
  have hadjBits := checkAdjBits_spec fc.adjMat rc.r (rc.n - rc.r) u.adjMasks hstr.1.1.2
  have hadjMasks_len := (extractMasks_spec _ _ u.h_adjMasks).1
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx
    have hxn : x < rc.n := by omega
    have hs := hadjSpec x hxn
    have hrow_eq : (rc.adj.toList.map Array.toList)[x]'(by omega) = (rc.adj[x]'(by omega)).toList := by simp
    rw [hrow_eq] at hs
    refine ⟨hs.1, fun v hv => ?_⟩
    have := hs.2.1 v hv
    omega
  · intro x hx y hy
    have hxn : x < rc.n := by omega
    have hyn : y < rc.n := by omega
    rw [hcadj x hxn y hyn]
    simp
  · intro x hx y hy
    have hxn : x < rc.n := by omega
    have hyn : y < rc.n := by omega
    have hmem_x := (hadjSpec x hxn).2.1
    refine ⟨?_, ?_⟩
    · dsimp [c, configOfRConf, Math.symAdj]
      by_cases hxy : x < y
      · have hyx : ¬ y < x := by omega
        simp [hxy, hyx]
      · by_cases hyx : y < x
        · simp [hxy, hyx]
        · have heq : x = y := by omega
          subst heq; simp
    · rw [hcadj x hxn x hxn]
      rw [Bool.eq_false_iff]
      intro hc
      exact (hmem_x x (List.contains_iff_mem.mp hc)).2 rfl
  · intro iu hiu iv hiv
    have hint_n : c.interiorSize = rc.n - rc.r := rfl
    have hcr : c.ringSize = rc.r := rfl
    have hdrop_len : (u.adjMasks.drop rc.r).length = rc.n - rc.r := by
      rw [List.length_drop, hadjMasks_len, hadjL]
    have hiu' : iu < (u.adjMasks.drop rc.r).length := by omega
    have hbit := hadjBits iu hiu' iv (by omega)
    have hrx : rc.r + iu < rc.n := by omega
    have hry : rc.r + iv < rc.n := by omega
    have hms_lt : rc.r + iu < u.adjMasks.length := by rw [hadjMasks_len, hadjL]; exact hrx
    have hdrop_eq : (u.adjMasks.drop rc.r)[iu]'hiu' = listGetD 0 u.adjMasks (rc.r + iu) := by
      rw [List.getElem_drop, listGetD_eq_getElem 0 u.adjMasks hms_lt]
    rw [hbit, hdrop_eq, (hadjSpec (rc.r + iu) hrx).2.2 (rc.r + iv), hcr]
    exact (hcadj (rc.r + iu) hrx (rc.r + iv) hry).symm

/-- **Theorem 3:** Ring cycle, zero ring chords, and canonical ring-to-interior fans. -/
theorem fastConf_equiv_ring_and_fans (h : Nat) (hh : h < 633) :
    let rc := parsedRConfList[h]'(by rw [parsedRConfList_length]; exact hh)
    let c := configOfRConf rc
    let r := c.ringSize
    (∀ x < r, ∀ y < r, c.adj x y = true ↔ (y = (x + r - 1) % r ∨ y = (x + 1) % r)) ∧
    (∀ x (hx : x < r),
      let nbrs := (rc.adj[x]'(by
        have hsz : rc.adj.size = c.totalNodes := (fastConf_equiv_header h hh).2.2.2.2.2.2.2.2.2.2.2.1
        have htot : c.totalNodes = c.ringSize + c.interiorSize := rfl
        omega)).toList
      nbrs.length ≥ 3 ∧
      nbrs.head? = some ((x + 1) % r) ∧
      nbrs.getLast? = some ((x + r - 1) % r) ∧
      (∀ v ∈ (nbrs.drop 1).dropLast, r ≤ v) ∧
      (∃ v ≥ r, v < c.totalNodes ∧ c.adj x v = true)) := by
  intro rc c r
  have h_all : checkConfEquiv (Discharging.lookupFastConfRec h) rc = true := fastConf_equiv_all h hh
  obtain ⟨u⟩ := unpackCheckConfEquiv h_all
  obtain ⟨hadjL, _, _, hadjSpec, hcadj⟩ := adj_eq_of_unpacked u
  have htot : c.totalNodes = rc.n := (fastConf_equiv_header h hh).2.2.2.2.1
  have hadj_sz : rc.adj.size = c.totalNodes := (fastConf_equiv_header h hh).2.2.2.2.2.2.2.2.2.2.2.1
  have hi4 : 4 ≤ c.interiorSize := (fastConf_equiv_header h hh).2.2.2.2.2.2.2.1
  have hr_eq : r = rc.r := rfl
  have hrn : r ≤ rc.n := by
    have : c.interiorSize = rc.n - r := rfl
    omega
  have hadjMasks_len := (extractMasks_spec _ _ u.h_adjMasks).1
  have hstr := u.h_str
  dsimp [checkStructureEquiv] at hstr
  simp only [Bool.and_eq_true] at hstr
  have hring := checkRingLoop_spec rc.r 0 u.adjMasks (rc.adj.toList.map Array.toList) hadjMasks_len.symm hstr.2
  refine ⟨?_, ?_⟩
  · intro x hx y hy
    have hxn : x < rc.n := by omega
    have hyn : y < rc.n := by omega
    have hx_ms : x < u.adjMasks.length := by rw [hadjMasks_len, hadjL]; exact hxn
    obtain ⟨hmask, _, _, _, _⟩ := hring x hx_ms (by omega)
    have hbit := congrArg (fun z => z.testBit y) hmask
    have hy' : y < rc.r := hr_eq ▸ hy
    simp only [Nat.zero_add, Nat.testBit_and, Nat.testBit_or, testBit_one_shiftLeft] at hbit
    rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one, decide_eq_true hy', Bool.and_true] at hbit
    have hx_adj := (hadjSpec x hxn).2.2 y
    rw [listGetD_eq_getElem 0 u.adjMasks hx_ms] at hx_adj
    rw [hcadj x hxn y hyn, ← hx_adj, hbit]
    simp only [Bool.or_eq_true, decide_eq_true_eq, hr_eq]
    constructor
    · rintro (h1 | h1)
      · exact Or.inl h1.symm
      · exact Or.inr h1.symm
    · rintro (h1 | h1)
      · exact Or.inl h1.symm
      · exact Or.inr h1.symm
  · intro x hx
    have hxn : x < rc.n := by omega
    have hx_ms : x < u.adjMasks.length := by rw [hadjMasks_len, hadjL]; exact hxn
    obtain ⟨_, hlen, hhd, hlast, hmid⟩ := hring x hx_ms (by omega)
    have hrow_eq : (rc.adj.toList.map Array.toList)[x]'(by omega) = (rc.adj[x]'(by omega)).toList := by simp
    simp only [Nat.zero_add, hrow_eq] at hlen hhd hlast hmid
    refine ⟨hlen, by simpa [hr_eq] using hhd, by simpa [hr_eq] using hlast, fun v hv => by simpa [hr_eq] using hmid v hv, ?_⟩
    rcases hn : (rc.adj[x]'(by omega)).toList with _ | ⟨a, _ | ⟨b, _ | ⟨d, rest⟩⟩⟩
    · simp [hn] at hlen
    · simp [hn] at hlen
    · simp [hn] at hlen
    · have hb_in_mid : b ∈ ((rc.adj[x]'(by omega)).toList.drop 1).dropLast := by
        rw [hn]; simp
      have hb_r : rc.r ≤ b := hmid b hb_in_mid
      have hb_in : b ∈ (rc.adj[x]'(by omega)).toList := by rw [hn]; simp
      have hb_lt : b < rc.n := ((hadjSpec x hxn).2.1 b (by simpa [hrow_eq] using hb_in)).1
      refine ⟨b, by omega, by omega, ?_⟩
      rw [hcadj x hxn b hb_lt, hrow_eq]
      exact List.contains_iff_mem.mpr hb_in

/-- **Theorem 4:** Interior vertices `fc.intVerts` have degrees `5..11`, `d ≤ 8 ∨ u = fc.z0`,
and exact cyclic adjacent triangles `iv.cyc`. -/
theorem fastConf_equiv_intVerts (h : Nat) (hh : h < 633) :
    let fc := Discharging.lookupFastConfRec h
    let rc := parsedRConfList[h]'(by rw [parsedRConfList_length]; exact hh)
    let c := configOfRConf rc
    let r := c.ringSize
    ∀ iu (hiu : iu < c.interiorSize),
      let iv := fc.intVerts[iu]'(by rw [(fastConf_equiv_header h hh).2.2.2.2.2.2.2.2.2.2.1]; exact hiu)
      let u0 := r + iu
      let nbrs := (rc.adj[u0]'(by
        have hsz : rc.adj.size = c.totalNodes := (fastConf_equiv_header h hh).2.2.2.2.2.2.2.2.2.2.2.1
        have htot : c.totalNodes = c.ringSize + c.interiorSize := rfl
        omega)).toList
      iv.u = u0 + 1 ∧
      iv.d = nbrs.length ∧
      5 ≤ iv.d ∧ iv.d ≤ 11 ∧
      (iv.d ≤ 8 ∨ iv.u = fc.z0) ∧
      nbrs.countP (· ≥ r) ≥ 2 ∧
      (∃ cp ∈ iv.cyc, cp.v > r ∧ cp.w > r) ∧
      iv.cyc.length = nbrs.length ∧
      (∀ j (hj : j < nbrs.length) (hjc : j < iv.cyc.length),
        iv.cyc[j]'hjc =
          CycPair.mk (nbrs[j] + 1)
            (if hj1 : j + 1 < nbrs.length then nbrs[j + 1] + 1 else nbrs[0] + 1)) ∧
      (∀ cp ∈ iv.cyc,
        1 ≤ cp.v ∧ cp.v ≤ c.totalNodes ∧ 1 ≤ cp.w ∧ cp.w ≤ c.totalNodes ∧
        c.adj u0 (cp.v - 1) = true ∧ c.adj u0 (cp.w - 1) = true ∧
        c.adj (cp.v - 1) (cp.w - 1) = true) := by
  intro fc rc c r iu hiu
  have h_all : checkConfEquiv fc rc = true := fastConf_equiv_all h hh
  obtain ⟨u⟩ := unpackCheckConfEquiv h_all
  obtain ⟨hadjL, _, hadjMasks_len, hadjSpec, hcadj⟩ := adj_eq_of_unpacked u
  have htot : c.totalNodes = rc.n := (fastConf_equiv_header h hh).2.2.2.2.1
  have hadj_sz : rc.adj.size = c.totalNodes := (fastConf_equiv_header h hh).2.2.2.2.2.2.2.2.2.2.2.1
  have hiv_len : fc.intVerts.length = c.interiorSize := (fastConf_equiv_header h hh).2.2.2.2.2.2.2.2.2.2.1
  have hr_eq : r = rc.r := rfl
  have hint_eq : c.interiorSize = rc.n - rc.r := rfl
  have hstr := u.h_str
  dsimp [checkStructureEquiv] at hstr
  simp only [Bool.and_eq_true] at hstr
  have hiv_loop := hstr.1.2
  rw [dropN_eq_drop] at hiv_loop
  have hdrop_len : ((rc.adj.toList.map Array.toList).drop rc.r).length = rc.n - rc.r := by
    rw [List.length_drop, hadjL]
  have hiu_drop : iu < ((rc.adj.toList.map Array.toList).drop rc.r).length := by omega
  have hiv := checkIntVertsLoop_spec fc rc.r u.adjMasks rc.contractEdges.toList rc.r
    ((rc.adj.toList.map Array.toList).drop rc.r) fc.intVerts hiv_loop iu hiu_drop
  rcases hiv with ⟨hu, hd, hd5, hd11, hd8, hcnt, hcyc_int, ⟨f0, rest, hnbrs_cons, hm⟩, htri⟩
  have hdrop_eq : ((rc.adj.toList.map Array.toList).drop rc.r)[iu]'hiu_drop =
      (rc.adj[rc.r + iu]'(by omega)).toList := by
    rw [List.getElem_drop]; simp
  have hlen_cyc := checkCycMatch_len f0 _ _ hm
  have hget_cyc := checkCycMatch_get f0 _ _ hm
  have hu0n : rc.r + iu < rc.n := by omega
  have hadj_u0 := hadjSpec (rc.r + iu) hu0n
  have hrow_u0 : (rc.adj.toList.map Array.toList)[rc.r + iu]'(by omega) = (rc.adj[rc.r + iu]'(by omega)).toList := by simp
  rw [hrow_u0] at hadj_u0
  refine ⟨by simpa [hr_eq] using hu, by simpa [hr_eq, hdrop_eq] using hd,
    by omega, by omega,
    by rw [hd]; exact hd8,
    by simpa [hr_eq, hdrop_eq] using hcnt, by simpa [hr_eq] using hcyc_int, ?_, ?_, ?_⟩
  · simpa [hr_eq, hdrop_eq] using hlen_cyc
  · intro j hj _hjc
    have hj' : j < ((rc.adj.toList.map Array.toList).drop rc.r)[iu].length := by
      simpa [hr_eq, hdrop_eq] using hj
    have hgj := hget_cyc j hj'
    have hlen_u0 : 5 ≤ (rc.adj[rc.r + iu]'(by omega)).toList.length := by
      simpa [hdrop_eq] using hd5
    have hfirst0 : f0 = (rc.adj[rc.r + iu]'(by omega)).toList[0]'(by omega) := by
      have := congrArg (·[0]?) hnbrs_cons
      rw [hdrop_eq] at this
      simp [List.getElem?_eq_getElem (by omega : 0 < (rc.adj[rc.r + iu]'(by omega)).toList.length)] at this
      exact this.symm
    rw [hgj]
    congr 1
    · congr 1; simp [hr_eq, hdrop_eq]
    · by_cases h1 : j + 1 < ((rc.adj.toList.map Array.toList).drop rc.r)[iu].length
      · have h2 : j + 1 < (rc.adj[r + iu]'(by omega)).toList.length := by simpa [hr_eq, hdrop_eq] using h1
        rw [dif_pos h1, dif_pos h2]
        simp [hr_eq, hdrop_eq]
      · have h2 : ¬ j + 1 < (rc.adj[r + iu]'(by omega)).toList.length := by simpa [hr_eq, hdrop_eq] using h1
        rw [dif_neg h1, dif_neg h2]
        simp [hr_eq, hfirst0]
  · intro cp hcp
    rcases List.mem_iff_getElem.mp hcp with ⟨j, hj, hcpj⟩
    have hj_d : j < ((rc.adj.toList.map Array.toList).drop rc.r)[iu].length := by
      rw [hlen_cyc] at hj; exact hj
    have hgj := hget_cyc j hj_d
    rw [← hcpj, hgj]
    have hv0 : ((rc.adj.toList.map Array.toList).drop rc.r)[iu][j] < rc.n := by
      have hm_mem : ((rc.adj.toList.map Array.toList).drop rc.r)[iu][j] ∈ (rc.adj[rc.r + iu]'(by omega)).toList := by
        rw [← hdrop_eq]; exact List.getElem_mem _
      exact (hadj_u0.2.1 _ hm_mem).1
    have hw0 : (if hj1 : j + 1 < ((rc.adj.toList.map Array.toList).drop rc.r)[iu].length then
        ((rc.adj.toList.map Array.toList).drop rc.r)[iu][j + 1] else f0) < rc.n := by
      by_cases hj1 : j + 1 < ((rc.adj.toList.map Array.toList).drop rc.r)[iu].length
      · rw [dif_pos hj1]
        have hm_mem : ((rc.adj.toList.map Array.toList).drop rc.r)[iu][j + 1] ∈ (rc.adj[rc.r + iu]'(by omega)).toList := by
          rw [← hdrop_eq]; exact List.getElem_mem _
        exact (hadj_u0.2.1 _ hm_mem).1
      · rw [dif_neg hj1]
        have hm_mem : f0 ∈ (rc.adj[rc.r + iu]'(by omega)).toList := by
          rw [← hdrop_eq, hnbrs_cons]; exact List.mem_cons_self
        exact (hadj_u0.2.1 _ hm_mem).1
    have hct := (checkCycTri_spec u.adjMasks rc.contractEdges.toList (rc.r + iu) _ htri cp hcp).1
    rw [← hcpj, hgj] at hct
    dsimp at hct ⊢
    have hv_in : ((rc.adj.toList.map Array.toList).drop rc.r)[iu][j] ∈ (rc.adj[rc.r + iu]'(by omega)).toList := by
      rw [← hdrop_eq]; exact List.getElem_mem _
    have hw_in : (if hj1 : j + 1 < ((rc.adj.toList.map Array.toList).drop rc.r)[iu].length then
        ((rc.adj.toList.map Array.toList).drop rc.r)[iu][j + 1] else f0) ∈ (rc.adj[rc.r + iu]'(by omega)).toList := by
      by_cases hj1 : j + 1 < ((rc.adj.toList.map Array.toList).drop rc.r)[iu].length
      · rw [dif_pos hj1, ← hdrop_eq]; exact List.getElem_mem _
      · rw [dif_neg hj1, ← hdrop_eq, hnbrs_cons]; exact List.mem_cons_self
    have hv_lt_m : ((rc.adj.toList.map Array.toList).drop rc.r)[iu][j] < u.adjMasks.length := by
      rw [hadjMasks_len]; exact hv0
    rw [listGetD_eq_getElem 0 u.adjMasks hv_lt_m] at hct
    have h_w_succ : (if hj1 : j + 1 < ((rc.adj.toList.map Array.toList).drop rc.r)[iu].length then
        ((rc.adj.toList.map Array.toList).drop rc.r)[iu][j + 1] + 1 else f0 + 1) =
        (if hj1 : j + 1 < ((rc.adj.toList.map Array.toList).drop rc.r)[iu].length then
        ((rc.adj.toList.map Array.toList).drop rc.r)[iu][j + 1] else f0) + 1 := by
      by_cases hj1 : j + 1 < ((rc.adj.toList.map Array.toList).drop rc.r)[iu].length
      · rw [dif_pos hj1, dif_pos hj1]
      · rw [dif_neg hj1, dif_neg hj1]
    have hv_spec := (hadjSpec _ hv0).2.2
    rw [listGetD_eq_getElem 0 u.adjMasks hv_lt_m] at hv_spec
    rw [h_w_succ] at hct ⊢
    rw [Nat.add_sub_cancel] at hct ⊢
    rw [hv_spec _, ← hcadj _ hv0 _ hw0] at hct
    refine ⟨by omega, by omega, by omega, by omega, ?_, ?_, ?_⟩
    · rw [hr_eq, hcadj (rc.r + iu) hu0n _ hv0, hrow_u0]
      exact List.contains_iff_mem.mpr hv_in
    · rw [hr_eq, hcadj (rc.r + iu) hu0n _ hw0, hrow_u0]
      exact List.contains_iff_mem.mpr hw_in
    · exact hct

/-- **Theorem 5:** `fc.z0`, `fc.z1`, and `fc.qSteps` cover all interior vertices without duplicates
and verify oriented triangles in `c`. -/
theorem fastConf_equiv_qSteps (h : Nat) (hh : h < 633) :
    let fc := Discharging.lookupFastConfRec h
    let c := configOfRConf (parsedRConfList[h]'(by rw [parsedRConfList_length]; exact hh))
    let zs := fc.z0 :: fc.z1 :: fc.qSteps.map (·.z)
    zs.Nodup ∧
    (∀ u, c.ringSize ≤ u → u < c.totalNodes → u + 1 ∈ zs) ∧
    (∀ qs ∈ fc.qSteps,
      1 ≤ qs.u ∧ qs.u ≤ c.totalNodes ∧
      1 ≤ qs.v ∧ qs.v ≤ c.totalNodes ∧
      1 ≤ qs.z ∧ qs.z ≤ c.totalNodes ∧
      qs.u ≠ qs.v ∧ qs.v ≠ qs.z ∧ qs.u ≠ qs.z ∧
      c.adj (qs.u - 1) (qs.v - 1) = true ∧
      c.adj (qs.v - 1) (qs.z - 1) = true ∧
      c.adj (qs.u - 1) (qs.z - 1) = true) := by
  intro fc c zs
  let rc := parsedRConfList[h]'(by rw [parsedRConfList_length]; exact hh)
  have h_all : checkConfEquiv fc rc = true := fastConf_equiv_all h hh
  obtain ⟨u⟩ := unpackCheckConfEquiv h_all
  obtain ⟨_, _, _, hadjSpec, hcadj⟩ := adj_eq_of_unpacked u
  have htot : c.totalNodes = rc.n := (fastConf_equiv_header h hh).2.2.2.2.1
  have hcr : c.ringSize = rc.r := rfl
  have hqs := u.h_qs
  dsimp [checkQStepEquiv] at hqs
  simp only [Bool.and_eq_true] at hqs
  have h_zm := hqs.1.2
  have h_qsloop := checkQStepsLoop_spec fc _ _ u.adjMasks fc.qSteps hqs.2
  cases hnm : nbrMaskNodup zs 0 with
  | none =>
    have hnm' : nbrMaskNodup (fc.z0 :: fc.z1 :: fc.qSteps.map (fun x => x.z)) 0 = none := hnm
    rw [hnm'] at h_zm; cases h_zm
  | some zm =>
    have hnm' : nbrMaskNodup (fc.z0 :: fc.z1 :: fc.qSteps.map (fun x => x.z)) 0 = some zm := hnm
    rw [hnm'] at h_zm
    simp only [beq_iff_eq] at h_zm
    obtain ⟨hnodup, _, hbits⟩ := nbrMaskNodup_spec zs 0 zm hnm
    refine ⟨hnodup, ?_, ?_⟩
    · intro x hrx hxt
      have hiu : x - rc.r < rc.n - rc.r := by omega
      have hbit := congrArg (fun z => z.testBit (x - rc.r)) h_zm
      have hm1 : ((1 <<< (rc.n - rc.r)) - 1).testBit (x - rc.r) = true := by
        rw [Nat.one_shiftLeft, Nat.testBit_two_pow_sub_one]; exact decide_eq_true hiu
      simp only [Nat.testBit_and, Nat.testBit_shiftRight, hm1, Bool.and_true] at hbit
      have hidx : rc.r + 1 + (x - rc.r) = x + 1 := by omega
      rw [hidx, hbits (x + 1)] at hbit
      simp only [Nat.zero_testBit, Bool.false_or] at hbit
      exact List.contains_iff_mem.mp hbit
    · intro qs hqsm
      obtain ⟨hu1, hun, hv1, hvn, hz1, hzn, huv, hvz, huz, e1, e2, e3⟩ := h_qsloop qs hqsm
      have hu0 : qs.u - 1 < rc.n := by omega
      have hv0 : qs.v - 1 < rc.n := by omega
      have hz0 : qs.z - 1 < rc.n := by omega
      have he1 : c.adj (qs.u - 1) (qs.v - 1) = true := by
        rw [hcadj _ hu0 _ hv0, ← (hadjSpec _ hu0).2.2 (qs.v - 1)]
        exact e1
      have he2 : c.adj (qs.v - 1) (qs.z - 1) = true := by
        rw [hcadj _ hv0 _ hz0, ← (hadjSpec _ hv0).2.2 (qs.z - 1)]
        exact e2
      have he3 : c.adj (qs.u - 1) (qs.z - 1) = true := by
        rw [hcadj _ hu0 _ hz0, ← (hadjSpec _ hu0).2.2 (qs.z - 1)]
        exact e3
      exact ⟨hu1, by omega, hv1, by omega, hz1, by omega, huv, hvz, huz, he1, he2, he3⟩

/-- **Theorem 6:** RSST `(3.6)` contract edge bounds, no ring-ring contracts, triangle sparsity,
and no shortcut edge in any contract-connected component across all 633 configurations. -/
theorem fastConf_equiv_contract_safe (h : Nat) (hh : h < 633) :
    let fc := Discharging.lookupFastConfRec h
    let rc := parsedRConfList[h]'(by rw [parsedRConfList_length]; exact hh)
    let c := configOfRConf rc
    let ce := c.contractEdges
    rc.contract = ce.length ∧ ce.length ≤ 4 ∧
    (∀ p ∈ ce, p.1 < c.totalNodes ∧ p.2 < c.totalNodes ∧ p.1 ≠ p.2 ∧
      c.adj p.1 p.2 = true ∧ ¬(p.1 < c.ringSize ∧ p.2 < c.ringSize)) ∧
    (∀ x < c.ringSize, (ce.filter fun p => p.1 == x || p.2 == x).length ≤ 1) ∧
    (∀ iv ∈ fc.intVerts, ∀ cp ∈ iv.cyc,
      (if isContractPair ce (iv.u - 1) (cp.v - 1) then 1 else 0) +
      (if isContractPair ce (iv.u - 1) (cp.w - 1) then 1 else 0) +
      (if isContractPair ce (cp.v - 1) (cp.w - 1) then 1 else 0) ≤ 1) ∧
    (∀ x < c.totalNodes, ∀ y < c.totalNodes,
      ContractReach ce x y → c.adj x y = true → isContractPair ce x y = true) := by
  intro fc rc c ce
  have h_all : checkConfEquiv fc rc = true := fastConf_equiv_all h hh
  obtain ⟨u⟩ := unpackCheckConfEquiv h_all
  obtain ⟨hadjL, _, _, hadjSpec, hcadj⟩ := adj_eq_of_unpacked u
  have htot : c.totalNodes = rc.n := (fastConf_equiv_header h hh).2.2.2.2.1
  have hiv_len : fc.intVerts.length = c.interiorSize := (fastConf_equiv_header h hh).2.2.2.2.2.2.2.2.2.2.1
  have hcr : c.ringSize = rc.r := rfl
  have hci : c.interiorSize = rc.n - rc.r := rfl
  have hce := u.h_ce
  dsimp [checkContractSafety] at hce
  change (rc.contract == ce.length && rc.contract ≤ 4 &&
    (match ce with
     | [] => true
     | _ :: _ =>
       checkCEEdges rc.r rc.n u.adjMasks ce &&
       checkContractRingDeg ce rc.r &&
       checkCELoops ce 0 (rc.adj.toList.map Array.toList))) = true at hce
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hce
  rcases hce with ⟨⟨hcon_len, hcon4⟩, hce_match⟩
  have hstr := u.h_str
  dsimp [checkStructureEquiv] at hstr
  simp only [Bool.and_eq_true] at hstr
  have hiv_loop := hstr.1.2
  rw [dropN_eq_drop] at hiv_loop
  by_cases hce_nil : ce = []
  · refine ⟨hcon_len, by rw [hce_nil]; simp, ?_, ?_, ?_, ?_⟩
    · intro p hp; rw [hce_nil] at hp; cases hp
    · intro x _; rw [hce_nil]; simp
    · intro iv _ cp _; rw [hce_nil]; simp [isContractPair]
    · intro x hx y hy hreach hadj_xy
      rw [hce_nil] at hreach
      have hxy : x = y := contractReach_nil hreach
      subst hxy
      have hself := (fastConf_equiv_adj h hh).2.2.1 x hx x hx
      rw [hself.2] at hadj_xy
      cases hadj_xy
  · rcases List.exists_cons_of_ne_nil hce_nil with ⟨p0, ps0, hce_cons⟩
    have hce_match' := hce_match
    rw [hce_cons] at hce_match'
    dsimp at hce_match'
    simp only [Bool.and_eq_true] at hce_match'
    rw [← hce_cons] at hce_match'
    rcases hce_match' with ⟨⟨hce_edges, hring_deg⟩, hce_loops⟩
    have hce_edges_spec := checkCEEdges_spec rc.r rc.n u.adjMasks ce hce_edges
    have hring_deg_spec := checkContractRingDeg_spec ce rc.r hring_deg
    have hce_loops_spec := checkCELoops_spec ce 0 _ hce_loops
    refine ⟨hcon_len, by omega, ?_, ?_, ?_, ?_⟩
    · intro q hq
      obtain ⟨hp1, hp2, hne, hadj_bit, hnrr⟩ := hce_edges_spec q hq
      have hcadj_q : c.adj q.1 q.2 = true := by
        rw [hcadj q.1 hp1 q.2 hp2, ← (hadjSpec q.1 hp1).2.2 q.2]
        exact hadj_bit
      exact ⟨by omega, by omega, hne, hcadj_q, by simpa [hcr] using hnrr⟩
    · exact hring_deg_spec
    · intro iv hiv cp hcp
      rcases List.mem_iff_getElem.mp hiv with ⟨iu, hiu, hiv_eq⟩
      have hiu' : iu < ((rc.adj.toList.map Array.toList).drop rc.r).length := by
        rw [List.length_drop, hadjL]; omega
      have hiv_spec := checkIntVertsLoop_spec fc rc.r u.adjMasks ce rc.r
        ((rc.adj.toList.map Array.toList).drop rc.r) fc.intVerts hiv_loop iu hiu'
      have hiv_u : iv.u = rc.r + iu + 1 := by rw [← hiv_eq]; exact hiv_spec.1
      have htri := hiv_spec.2.2.2.2.2.2.2.2
      rw [hiv_eq] at htri
      have hct := (checkCycTri_spec u.adjMasks ce (rc.r + iu) iv.cyc htri cp hcp).2 hce_nil
      have : iv.u - 1 = rc.r + iu := by omega
      rw [this]
      exact hct
    · intro x hx y hy hreach hadj_xy
      have hxn : x < rc.n := by omega
      have hyn : y < rc.n := by omega
      have hy_in : y ∈ (rc.adj.toList.map Array.toList)[x]'(by omega) := by
        rw [hcadj x hxn y hyn] at hadj_xy
        exact List.contains_iff_mem.mp hadj_xy
      have hne : y ≠ x := ((hadjSpec x hxn).2.1 y hy_in).2
      have hreach' : ContractReach ce (0 + x) y := by simpa using hreach
      have hres := hce_loops_spec x (by omega) y hy_in (by omega) hreach'
      simpa using hres

end Math.Unavoidability
