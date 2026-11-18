module

/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
All rights reserved.
Released under Apache 2.0 license.

Stage R.2: Soundness of `rootedSubConfRec` + `checkIsoRec` into a faithful
hypermap triangulation embedding (`AppearsInTriangulation`).
-/
public import FourColorTheorem.Math.Unavoidability.AllDegreesDischarge
public import FourColorTheorem.Math.Unavoidability.ConfGeomCert
public import FourColorTheorem.Math.Unavoidability.FastConfEquiv

@[expose] public section

attribute [-simp] Nat.lor_eq Nat.land_eq Nat.xor_eq Nat.shiftLeft_eq' Nat.shiftRight_eq'

namespace Math.Unavoidability

open Math.Discharging Math.Hypermap

section QStepRingZCert

/-- Every `QStep` placing a ring vertex (`q.z ≤ fc.ring`) has both parent vertices in the interior. -/
def checkQStepRingZ (fc : FastConf) : Bool :=
  fc.qSteps.all (fun q => q.z > fc.ring || (q.u > fc.ring && q.v > fc.ring))

private theorem qStepRingZ_row0 : fastConfTable[0]!.all (fun b => b.all checkQStepRingZ) = true := rfl
private theorem qStepRingZ_row1 : fastConfTable[1]!.all (fun b => b.all checkQStepRingZ) = true := rfl
private theorem qStepRingZ_row2 : fastConfTable[2]!.all (fun b => b.all checkQStepRingZ) = true := rfl
private theorem qStepRingZ_row3 : fastConfTable[3]!.all (fun b => b.all checkQStepRingZ) = true := rfl
private theorem qStepRingZ_row4 : fastConfTable[4]!.all (fun b => b.all checkQStepRingZ) = true := rfl
private theorem qStepRingZ_row5 : fastConfTable[5]!.all (fun b => b.all checkQStepRingZ) = true := rfl
private theorem qStepRingZ_row6 : fastConfTable[6]!.all (fun b => b.all checkQStepRingZ) = true := rfl
private theorem qStepRingZ_row7 : fastConfTable[7]!.all (fun b => b.all checkQStepRingZ) = true := rfl
private theorem qStepRingZ_row8 : fastConfTable[8]!.all (fun b => b.all checkQStepRingZ) = true := rfl
private theorem qStepRingZ_row9 : fastConfTable[9]!.all (fun b => b.all checkQStepRingZ) = true := rfl

private theorem qStepRingZ_row_of_lt (r0 : Nat) (hr0 : r0 < 10) :
    fastConfTable[r0]!.all (fun b => b.all checkQStepRingZ) = true := by
  have : r0 = 0 ∨ r0 = 1 ∨ r0 = 2 ∨ r0 = 3 ∨ r0 = 4 ∨
      r0 = 5 ∨ r0 = 6 ∨ r0 = 7 ∨ r0 = 8 ∨ r0 = 9 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact qStepRingZ_row0
  · exact qStepRingZ_row1
  · exact qStepRingZ_row2
  · exact qStepRingZ_row3
  · exact qStepRingZ_row4
  · exact qStepRingZ_row5
  · exact qStepRingZ_row6
  · exact qStepRingZ_row7
  · exact qStepRingZ_row8
  · exact qStepRingZ_row9

theorem fastConf_qStep_ringZ (h : Nat) (hh : h < 633) :
    checkQStepRingZ (lookupFastConfRec h) = true := by
  obtain ⟨hb0, hb1, hb2, hfc⟩ := lookupFastConfRec_eq_table h hh
  rw [hfc]
  have hr0 : h >>> 6 < 10 := by
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have hr1 : (h >>> 3 &&& 7) < 8 := by
    have hmask : (7 : Nat) = 2 ^ 3 - 1 := rfl
    rw [hmask, Nat.and_two_pow_sub_one_eq_mod]
    exact Nat.mod_lt _ (by decide)
  have hrow := qStepRingZ_row_of_lt (h >>> 6) hr0
  have hrow' : (fastConfTable[h >>> 6]'hb0).all (fun b => b.all checkQStepRingZ) = true := by
    rwa [← getElem!_pos fastConfTable (h >>> 6) hb0]
  have hblk := (List.all_eq_true.mp hrow') (fastConfTable[h >>> 6][h >>> 3 &&& 7]'hb1) (List.getElem_mem hb1)
  exact (List.all_eq_true.mp hblk) (fastConfTable[h >>> 6][h >>> 3 &&& 7][h &&& 7]'hb2) (List.getElem_mem hb2)

theorem qStep_ringZ_parents_int (h : Nat) (hh : h < 633) {q : QStep}
    (hq : q ∈ (lookupFastConfRec h).qSteps) (hle : q.z ≤ (lookupFastConfRec h).ring) :
    (lookupFastConfRec h).ring < q.u ∧ (lookupFastConfRec h).ring < q.v := by
  have hchk := fastConf_qStep_ringZ h hh
  have hq' := List.all_eq_true.mp hchk q hq
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hq'
  rcases hq' with hgt | ⟨hu, hv⟩
  · omega
  · exact ⟨hu, hv⟩

end QStepRingZCert

section GraphAndOrbitHelpers

/-- Decidable vertex adjacency between two dart-represented vertices of a hypermap. -/
def areAdjacentVertices (T : Hypermap) [DecidableEq T.Dart]
    (u v : T.Dart) (fuel : Nat) : Bool :=
  (getOrbit T.node fuel u).any (fun d => sameVertex T (T.edge.f d) v fuel)

theorem sameVertex_iff_mem_getOrbit (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel) (u d : T.Dart) :
    sameVertex T d u fuel = true ↔ d ∈ getOrbit T.node fuel u := by
  rw [sameVertex_symm_of_complete T darts h_all h_len d u]
  simp only [sameVertex, List.contains_iff_mem]

theorem sameVertex_node_f (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel) (d : T.Dart) :
    sameVertex T (T.node.f d) d fuel = true := by
  rw [sameVertex_iff_mem_getOrbit T darts h_all h_len]
  exact Hypermap.getOrbit_closed_under_f_of_complete T.node darts h_all h_len
    (Hypermap.mem_getOrbit_self T.node fuel d)

theorem sameVertex_node_inv (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel) (d : T.Dart) :
    sameVertex T (T.node.inv d) d fuel = true := by
  rw [sameVertex_iff_mem_getOrbit T darts h_all h_len]
  exact Hypermap.getOrbit_closed_under_inv_of_complete T.node darts h_all h_len
    (Hypermap.mem_getOrbit_self T.node fuel d)

theorem sameVertex_permOriented_f (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel) (orient : Bool) (d : T.Dart) :
    sameVertex T ((nodePermOriented T orient).f d) d fuel = true := by
  cases orient
  · exact sameVertex_node_f T darts h_all h_len d
  · exact sameVertex_node_inv T darts h_all h_len d

theorem sameVertex_permOriented_inv (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel) (orient : Bool) (d : T.Dart) :
    sameVertex T ((nodePermOriented T orient).inv d) d fuel = true := by
  cases orient
  · exact sameVertex_node_inv T darts h_all h_len d
  · exact sameVertex_node_f T darts h_all h_len d

theorem sameVertex_iter_permOriented (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel) (orient : Bool) (k : Nat) (d : T.Dart) :
    sameVertex T (Hypermap.Perm.iter (nodePermOriented T orient) k d) d fuel = true := by
  induction k generalizing d with
  | zero => exact sameVertex_refl T fuel d
  | succ k ih =>
      simp only [Hypermap.Perm.iter]
      exact sameVertex_trans_of_complete T darts h_all h_len
        (sameVertex_permOriented_f T darts h_all h_len orient _) (ih d)

theorem areAdjacentVertices_iff (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel) (u v : T.Dart) :
    areAdjacentVertices T u v fuel = true ↔
      ∃ d, sameVertex T d u fuel = true ∧ sameVertex T (T.edge.f d) v fuel = true := by
  simp only [areAdjacentVertices, List.any_eq_true, ← sameVertex_iff_mem_getOrbit T darts h_all h_len]

theorem areAdjacentVertices_of_dart (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel) {u v d : T.Dart}
    (hu : sameVertex T d u fuel = true) (hv : sameVertex T (T.edge.f d) v fuel = true) :
    areAdjacentVertices T u v fuel = true :=
  (areAdjacentVertices_iff T darts h_all h_len u v).mpr ⟨d, hu, hv⟩

theorem areAdjacentVertices_congr (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel) {u u' v v' : T.Dart}
    (hu : sameVertex T u u' fuel = true) (hv : sameVertex T v v' fuel = true) :
    areAdjacentVertices T u v fuel = areAdjacentVertices T u' v' fuel := by
  apply Bool.eq_iff_iff.mpr
  simp only [areAdjacentVertices_iff T darts h_all h_len]
  constructor
  · rintro ⟨d, hdu, hdv⟩
    exact ⟨d, sameVertex_trans_of_complete T darts h_all h_len hdu hu,
      sameVertex_trans_of_complete T darts h_all h_len hdv hv⟩
  · rintro ⟨d, hdu', hdv'⟩
    have hu' : sameVertex T u' u fuel = true := by
      rw [sameVertex_symm_of_complete T darts h_all h_len u' u]; exact hu
    have hv' : sameVertex T v' v fuel = true := by
      rw [sameVertex_symm_of_complete T darts h_all h_len v' v]; exact hv
    exact ⟨d, sameVertex_trans_of_complete T darts h_all h_len hdu' hu',
      sameVertex_trans_of_complete T darts h_all h_len hdv' hv'⟩

theorem areAdjacentVertices_symm (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel) (u v : T.Dart) :
    areAdjacentVertices T u v fuel = areAdjacentVertices T v u fuel := by
  apply Bool.eq_iff_iff.mpr
  simp only [areAdjacentVertices_iff T darts h_all h_len]
  constructor
  · rintro ⟨d, hdu, hdv⟩
    refine ⟨T.edge.f d, hdv, ?_⟩
    rw [T.edge_edge]
    exact hdu
  · rintro ⟨d, hdv, hdu⟩
    refine ⟨T.edge.f d, hdu, ?_⟩
    rw [T.edge_edge]
    exact hdv

theorem areAdjacentVertices_irrefl (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel)
    (h_loopless : ∀ d : T.Dart, sameVertex T d (T.edge.f d) fuel = false) (u : T.Dart) :
    areAdjacentVertices T u u fuel = false := by
  apply Bool.eq_false_iff.mpr
  intro hadj
  rw [areAdjacentVertices_iff T darts h_all h_len] at hadj
  rcases hadj with ⟨d, hdu, hedu⟩
  have heu' : sameVertex T u (T.edge.f d) fuel = true := by
    rw [sameVertex_symm_of_complete T darts h_all h_len u (T.edge.f d)]; exact hedu
  have hsame := sameVertex_trans_of_complete T darts h_all h_len hdu heu'
  rw [h_loopless d] at hsame
  exact Bool.false_ne_true hsame

theorem tri_fan_turn (T : Hypermap) (h_tri : ∀ x : T.Dart, T.face.f (T.face.f (T.face.f x)) = x)
    (refl : Bool) (d : T.Dart) :
    T.edge.f ((nodePermOriented T refl).inv (T.edge.f d)) =
      (nodePermOriented T refl).f (T.edge.f ((nodePermOriented T refl).f d)) := by
  cases refl
  · exact edge_node_inv_edge_eq_node_f_edge_node_f T h_tri d
  · simp only [nodePermOriented, Perm.symm]
    have h1 := edge_node_inv_edge_eq_node_f_edge_node_f T h_tri (T.node.inv d)
    rw [T.node.right_inv] at h1
    have h2 := congrArg T.edge.f h1
    rw [T.edge_edge] at h2
    exact h2.symm

theorem tri_fan_turn_edge (T : Hypermap) (h_tri : ∀ x : T.Dart, T.face.f (T.face.f (T.face.f x)) = x)
    (refl : Bool) (d : T.Dart) :
    T.edge.f ((nodePermOriented T refl).f (T.edge.f ((nodePermOriented T refl).f d))) =
      (nodePermOriented T refl).inv (T.edge.f d) := by
  rw [← tri_fan_turn T h_tri refl d, T.edge_edge]

theorem nodePermOriented_orbit_length (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel) (orient : Bool) (d : T.Dart) :
    (getOrbit (nodePermOriented T orient) fuel d).length = nodeDegree T d fuel := by
  cases orient
  · rfl
  · exact Hypermap.getOrbit_symm_length_eq_of_complete T.node darts h_all h_len d

theorem perm_iter_nodePermOriented_deg_eq_self (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel) (orient : Bool) (d : T.Dart) :
    Hypermap.Perm.iter (nodePermOriented T orient) (nodeDegree T d fuel) d = d := by
  cases orient
  · exact Hypermap.perm_iter_length_getOrbit_eq_self_of_complete T.node darts h_all h_len d
  · exact Hypermap.perm_iter_symm_length_getOrbit_eq_self_of_complete T.node darts h_all h_len d

private theorem iterList_getElem {D : Type} [DecidableEq D] (p : Perm D) (d : D) (n i : Nat) (hi : i < n) :
    (Hypermap.iterList p d n)[i]'(by rw [Hypermap.iterList_length]; exact hi) =
      Hypermap.Perm.iter p i d := by
  induction n generalizing d i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => rfl
      | succ i =>
          simp only [Hypermap.iterList, List.getElem_cons_succ]
          rw [ih (p.f d) i (by omega), ← Hypermap.Perm.iter_succ_right]

private theorem nodup_getElem_inj {α : Type} {l : List α} (h : l.Nodup) {i j : Nat}
    (hi : i < l.length) (hj : j < l.length) (heq : l[i] = l[j]) : i = j := by
  induction l generalizing i j with
  | nil => simp at hi
  | cons a t ih =>
      rw [List.nodup_cons] at h
      cases i with
      | zero =>
          cases j with
          | zero => rfl
          | succ j =>
              exfalso; apply h.1
              have hmem : t[j]'(by simp at hj; omega) ∈ t := List.getElem_mem _
              simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
              simpa [← heq] using hmem
      | succ i =>
          cases j with
          | zero =>
              exfalso; apply h.1
              have hmem : t[i]'(by simp at hi; omega) ∈ t := List.getElem_mem _
              simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
              simpa [heq] using hmem
          | succ j =>
              congr 1
              exact ih h.2 (by simp at hi; omega) (by simp at hj; omega)
                (by simpa [List.getElem_cons_succ] using heq)

private theorem getElem_eq_of_list_eq {α : Type} {l1 l2 : List α} (h : l1 = l2) (i : Nat)
    (h1 : i < l1.length) (h2 : i < l2.length) : l1[i]'h1 = l2[i]'h2 := by
  cases h; rfl

theorem perm_iter_nodePermOriented_inj_lt_deg (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel) (orient : Bool) (d : T.Dart)
    {m k : Nat} (hm : m < nodeDegree T d fuel) (hk : k < nodeDegree T d fuel)
    (heq : Hypermap.Perm.iter (nodePermOriented T orient) m d =
      Hypermap.Perm.iter (nodePermOriented T orient) k d) : m = k := by
  let P := nodePermOriented T orient
  let L := (getOrbit P fuel d).length
  have hlen : L = nodeDegree T d fuel :=
    nodePermOriented_orbit_length T darts h_all h_len orient d
  have hrev := Hypermap.getOrbit_eq_reverse_iterList_of_complete P darts h_all h_len d
  have hnodup : (getOrbit P fuel d).Nodup := Hypermap.getOrbit_nodup P fuel d
  have hm' : L - 1 - m < (getOrbit P fuel d).length := by omega
  have hk' : L - 1 - k < (getOrbit P fuel d).length := by omega
  have hm_rev : (getOrbit P fuel d)[L - 1 - m]'hm' = Hypermap.Perm.iter P m d := by
    have h1 : (Hypermap.iterList P d L).reverse[L - 1 - m]'(by
        rw [List.length_reverse, Hypermap.iterList_length]; exact hm') =
        (Hypermap.iterList P d L)[(Hypermap.iterList P d L).length - 1 - (L - 1 - m)]'(by
        rw [Hypermap.iterList_length]; omega) := List.getElem_reverse _
    have hidx : (Hypermap.iterList P d L).length - 1 - (L - 1 - m) = m := by
      rw [Hypermap.iterList_length]; omega
    calc (getOrbit P fuel d)[L - 1 - m]'hm'
        = (Hypermap.iterList P d L).reverse[L - 1 - m]'(by
            rw [List.length_reverse, Hypermap.iterList_length]; exact hm') :=
          getElem_eq_of_list_eq hrev (L - 1 - m) hm' _
      _ = (Hypermap.iterList P d L)[m]'(by rw [Hypermap.iterList_length]; omega) := by
          simp only [h1, hidx]
      _ = Hypermap.Perm.iter P m d := iterList_getElem P d L m (by omega)
  have hk_rev : (getOrbit P fuel d)[L - 1 - k]'hk' = Hypermap.Perm.iter P k d := by
    have h1 : (Hypermap.iterList P d L).reverse[L - 1 - k]'(by
        rw [List.length_reverse, Hypermap.iterList_length]; exact hk') =
        (Hypermap.iterList P d L)[(Hypermap.iterList P d L).length - 1 - (L - 1 - k)]'(by
        rw [Hypermap.iterList_length]; omega) := List.getElem_reverse _
    have hidx : (Hypermap.iterList P d L).length - 1 - (L - 1 - k) = k := by
      rw [Hypermap.iterList_length]; omega
    calc (getOrbit P fuel d)[L - 1 - k]'hk'
        = (Hypermap.iterList P d L).reverse[L - 1 - k]'(by
            rw [List.length_reverse, Hypermap.iterList_length]; exact hk') :=
          getElem_eq_of_list_eq hrev (L - 1 - k) hk' _
      _ = (Hypermap.iterList P d L)[k]'(by rw [Hypermap.iterList_length]; omega) := by
          simp only [h1, hidx]
      _ = Hypermap.Perm.iter P k d := iterList_getElem P d L k (by omega)
  have hget : (getOrbit P fuel d)[L - 1 - m]'hm' = (getOrbit P fuel d)[L - 1 - k]'hk' := by
    rw [hm_rev, hk_rev]; exact heq
  have hinj := nodup_getElem_inj hnodup hm' hk' hget
  omega

theorem mem_getOrbit_iff_exists_iter (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel) (p : Perm T.Dart) (d x : T.Dart) :
    x ∈ getOrbit p fuel d ↔
      ∃ m < (getOrbit p fuel d).length, x = Hypermap.Perm.iter p m d := by
  have hrev := Hypermap.getOrbit_eq_reverse_iterList_of_complete p darts h_all h_len d
  have hmem : x ∈ getOrbit p fuel d ↔ x ∈ (Hypermap.iterList p d (getOrbit p fuel d).length).reverse := by
    rw [← hrev]
  rw [hmem, List.mem_reverse, List.mem_iff_getElem]
  constructor
  · rintro ⟨m, hm, rfl⟩
    have hm' : m < (getOrbit p fuel d).length := by rw [Hypermap.iterList_length] at hm; exact hm
    exact ⟨m, hm', iterList_getElem p d _ m hm'⟩
  · rintro ⟨m, hm, rfl⟩
    refine ⟨m, by rw [Hypermap.iterList_length]; exact hm, iterList_getElem p d _ m hm⟩

theorem mem_getOrbit_node_iff_mem_symm (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel) (d x : T.Dart) :
    x ∈ getOrbit T.node fuel d ↔ x ∈ getOrbit T.node.symm fuel d := by
  have hlen : (getOrbit T.node.symm fuel d).length = (getOrbit T.node fuel d).length :=
    Hypermap.getOrbit_symm_length_eq_of_complete T.node darts h_all h_len d
  have hpos : 0 < (getOrbit T.node fuel d).length :=
    List.length_pos_of_mem (Hypermap.mem_getOrbit_self T.node fuel d)
  rw [mem_getOrbit_iff_exists_iter T darts h_all h_len T.node d x,
      mem_getOrbit_iff_exists_iter T darts h_all h_len T.node.symm d x, hlen]
  constructor
  · rintro ⟨m, hm, rfl⟩
    by_cases hm0 : m = 0
    · subst hm0; exact ⟨0, hpos, rfl⟩
    · let L := (getOrbit T.node fuel d).length
      refine ⟨L - m, by omega, ?_⟩
      have hL : Hypermap.Perm.iter T.node (L - m) (Hypermap.Perm.iter T.node m d) = d := by
        rw [← Hypermap.Perm.iter_add, Nat.sub_add_cancel (by omega)]
        exact Hypermap.perm_iter_length_getOrbit_eq_self_of_complete T.node darts h_all h_len d
      calc Hypermap.Perm.iter T.node m d
          = Hypermap.Perm.iter T.node.symm (L - m)
              (Hypermap.Perm.iter T.node (L - m) (Hypermap.Perm.iter T.node m d)) :=
            (Hypermap.Perm.iter_symm_left_inv T.node (L - m) _).symm
        _ = Hypermap.Perm.iter T.node.symm (L - m) d := by rw [hL]
  · rintro ⟨m, hm, rfl⟩
    by_cases hm0 : m = 0
    · subst hm0; exact ⟨0, hpos, rfl⟩
    · let L := (getOrbit T.node fuel d).length
      refine ⟨L - m, by omega, ?_⟩
      have hL : Hypermap.Perm.iter T.node.symm (L - m) (Hypermap.Perm.iter T.node.symm m d) = d := by
        rw [← Hypermap.Perm.iter_add, Nat.sub_add_cancel (by omega)]
        exact Hypermap.perm_iter_symm_length_getOrbit_eq_self_of_complete T.node darts h_all h_len d
      have hleft := Hypermap.Perm.iter_symm_left_inv T.node.symm (L - m) (Hypermap.Perm.iter T.node.symm m d)
      rw [Hypermap.Perm.symm_symm] at hleft
      calc Hypermap.Perm.iter T.node.symm m d
          = Hypermap.Perm.iter T.node (L - m)
              (Hypermap.Perm.iter T.node.symm (L - m) (Hypermap.Perm.iter T.node.symm m d)) := hleft.symm
        _ = Hypermap.Perm.iter T.node (L - m) d := by rw [hL]

theorem mem_getOrbit_nodePermOriented_iff (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel) (orient : Bool) (d x : T.Dart) :
    x ∈ getOrbit T.node fuel d ↔
      ∃ m < nodeDegree T d fuel, x = Hypermap.Perm.iter (nodePermOriented T orient) m d := by
  have hx_mem : x ∈ getOrbit T.node fuel d ↔ x ∈ getOrbit (nodePermOriented T orient) fuel d := by
    cases orient
    · exact Iff.rfl
    · exact mem_getOrbit_node_iff_mem_symm T darts h_all h_len d x
  rw [hx_mem, mem_getOrbit_iff_exists_iter T darts h_all h_len (nodePermOriented T orient) d x,
      nodePermOriented_orbit_length T darts h_all h_len orient d]

end GraphAndOrbitHelpers

section CartwheelCanonicalDarts

/-- Active cartwheel positions around a center dart of degree `deg` with spoke degrees `cartDeg`. -/
def activeCartPos (deg : Nat) (cartDeg : Nat → Nat) (p : Nat) : Prop :=
  p = 0 ∨ (1 ≤ p ∧ p ≤ 2 * deg) ∨
    (∃ i r, 1 ≤ i ∧ i ≤ deg ∧ (r = 2 ∨ r = 3 ∨ r = 4) ∧
      p = r * deg + i ∧ r + 4 ≤ cartDeg i ∧ cartDeg i ≤ 8)

/-- Undirected local adjacency in the RSST cartwheel neighborhood (`pureSpokeAdj`). -/
def pureCartAdj (deg : Nat) (cartDeg : Nat → Nat) (u v : Nat) : Prop :=
  ∃ i, 1 ≤ i ∧ i ≤ deg ∧
    (pureSpokeAdj deg i (cartDeg i) u v ≠ 63 ∨ pureSpokeAdj deg i (cartDeg i) v u ≠ 63)

/-- Faithfulness of a cartwheel around `d0` in an internally 6-connected triangulation `T`:
    (1) distinct active cartwheel positions map to distinct vertices of `T`;
    (2) any `T`-edge between distinct active cartwheel positions is a local `pureCartAdj` edge;
    (3) no parallel `T`-edges connect distinct active cartwheel positions. -/
def CartwheelEmbedded (T : Hypermap) [DecidableEq T.Dart]
    (fuel : Nat) (refl : Bool) (d0 : T.Dart) : Prop :=
  let deg := nodeDegree T d0 fuel
  let cartDeg := cartDegOriented T fuel deg refl d0
  (∀ p q, activeCartPos deg cartDeg p → activeCartPos deg cartDeg q → p ≠ q →
    sameVertex T (cartDartOriented T deg refl d0 p)
      (cartDartOriented T deg refl d0 q) fuel = false) ∧
  (∀ p q, activeCartPos deg cartDeg p → activeCartPos deg cartDeg q → p ≠ q →
    areAdjacentVertices T (cartDartOriented T deg refl d0 p)
      (cartDartOriented T deg refl d0 q) fuel = true →
    pureCartAdj deg cartDeg p q) ∧
  (∀ p q, activeCartPos deg cartDeg p → activeCartPos deg cartDeg q → p ≠ q →
    ∀ d1 d2,
      sameVertex T d1 (cartDartOriented T deg refl d0 p) fuel = true →
      sameVertex T d2 (cartDartOriented T deg refl d0 p) fuel = true →
      sameVertex T (T.edge.f d1) (cartDartOriented T deg refl d0 q) fuel = true →
      sameVertex T (T.edge.f d2) (cartDartOriented T deg refl d0 q) fuel = true →
      d1 = d2)

/-- Six oriented darts of an oriented triangle `(x, y, z)` generated by `gen : x → y`. -/
def triEdgeDart (T : Hypermap) (refl : Bool) (gen : T.Dart) (x y z u v : Nat) : Option T.Dart :=
  let P := nodePermOriented T refl
  let e := T.edge.f
  if (u == x && v == y) = true then some gen
  else if (u == x && v == z) = true then some (P.f gen)
  else if (u == y && v == x) = true then some (e gen)
  else if (u == y && v == z) = true then some (P.inv (e gen))
  else if (u == z && v == x) = true then some (e (P.f gen))
  else if (u == z && v == y) = true then some (P.f (e (P.f gen)))
  else none

/-- Oriented triangles (with `x → y` generator darts) of spoke `i` for spoke degree `k`.
    For `k ∉ {5, 6, 7, 8}` (`k ≥ 9`), the two base triangles `(0, h, i)` and `(i, h, a)` still exist. -/
def spokeTriSpecs (T : Hypermap) (deg : Nat) (refl : Bool) (d0 : T.Dart) (i k : Nat) :
    List (Nat × Nat × Nat × T.Dart) :=
  let P := nodePermOriented T refl
  let e := T.edge.f
  let h := if i = 1 then deg else i - 1
  let s_h := spokeDartOriented T refl d0 h
  let s_i := spokeDartOriented T refl d0 i
  let a := deg + h
  let b := deg + i
  let c := 2 * deg + i
  let d := 3 * deg + i
  let e_v := 4 * deg + i
  let d1 := P.f (e s_i)
  let d2 := Hypermap.Perm.iter P 2 (e s_i)
  let d3 := Hypermap.Perm.iter P 3 (e s_i)
  let d4 := Hypermap.Perm.iter P 4 (e s_i)
  let d5 := Hypermap.Perm.iter P 5 (e s_i)
  let base := [(0, h, i, s_h), (i, h, a, d1)]
  if k = 5 then base ++ [(i, a, b, d2)]
  else if k = 6 then base ++ [(i, a, c, d2), (i, c, b, d3)]
  else if k = 7 then base ++ [(i, a, c, d2), (i, c, d, d3), (i, d, b, d4)]
  else if k = 8 then base ++ [(i, a, c, d2), (i, c, d, d3), (i, d, e_v, d4), (i, e_v, b, d5)]
  else base

/-- Canonical dart lookup in spoke `i` of degree `k`. -/
def spokeEdgeDart (T : Hypermap) (deg : Nat) (refl : Bool) (d0 : T.Dart) (i k u v : Nat) :
    Option T.Dart :=
  (spokeTriSpecs T deg refl d0 i k).findSome? (fun (x, y, z, gen) => triEdgeDart T refl gen x y z u v)

/-- Canonical oriented dart for any cartwheel edge `(u, v)`. -/
def canonCartDart (T : Hypermap) (deg : Nat) (refl : Bool) (d0 : T.Dart)
    (cd : Nat → Nat) (u v : Nat) : T.Dart :=
  ((List.range' 1 deg).findSome? (fun i => spokeEdgeDart T deg refl d0 i (cd i) u v)).getD d0

theorem triEdgeDart_eq_some_iff {T : Hypermap} {refl : Bool} {gen : T.Dart}
    {x y z u v : Nat} {d : T.Dart}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    triEdgeDart T refl gen x y z u v = some d ↔
      (u = x ∧ v = y ∧ d = gen) ∨
      (u = x ∧ v = z ∧ d = (nodePermOriented T refl).f gen) ∨
      (u = y ∧ v = x ∧ d = T.edge.f gen) ∨
      (u = y ∧ v = z ∧ d = (nodePermOriented T refl).inv (T.edge.f gen)) ∨
      (u = z ∧ v = x ∧ d = T.edge.f ((nodePermOriented T refl).f gen)) ∨
      (u = z ∧ v = y ∧ d = (nodePermOriented T refl).f (T.edge.f ((nodePermOriented T refl).f gen))) := by
  dsimp only [triEdgeDart]
  simp only [Bool.and_eq_true, beq_iff_eq]
  constructor
  · intro h
    split at h
    · injection h with hd; exact Or.inl ⟨by omega, by omega, hd.symm⟩
    · split at h
      · injection h with hd; exact Or.inr (Or.inl ⟨by omega, by omega, hd.symm⟩)
      · split at h
        · injection h with hd; exact Or.inr (Or.inr (Or.inl ⟨by omega, by omega, hd.symm⟩))
        · split at h
          · injection h with hd; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, hd.symm⟩)))
          · split at h
            · injection h with hd; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨by omega, by omega, hd.symm⟩))))
            · split at h
              · injection h with hd; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨by omega, by omega, hd.symm⟩))))
              · cases h
  · rintro (⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
            ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩)
    · simp
    · simp [hyz.symm]
    · simp [hxy.symm]
    · simp [hxy.symm, hxz.symm]
    · simp [hxz.symm, hyz.symm]
    · simp [hxz.symm, hyz.symm, hxy.symm]

theorem triEdgeDart_edge (T : Hypermap) (h_tri : ∀ x : T.Dart, T.face.f (T.face.f (T.face.f x)) = x)
    (refl : Bool) (gen : T.Dart) {x y z u v : Nat} {d : T.Dart}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (h : triEdgeDart T refl gen x y z u v = some d) :
    triEdgeDart T refl gen x y z v u = some (T.edge.f d) := by
  rw [triEdgeDart_eq_some_iff hxy hyz hxz] at h ⊢
  rcases h with ⟨hu, hv, hd⟩ | ⟨hu, hv, hd⟩ | ⟨hu, hv, hd⟩ |
                ⟨hu, hv, hd⟩ | ⟨hu, hv, hd⟩ | ⟨hu, hv, hd⟩
  · exact Or.inr (Or.inr (Or.inl ⟨hv, hu, by rw [hd]⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, hu, by rw [hd]⟩))))
  · exact Or.inl ⟨hv, hu, by rw [hd, T.edge_edge]⟩
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hv, hu, by rw [hd, tri_fan_turn T h_tri refl gen]⟩))))
  · exact Or.inr (Or.inl ⟨hv, hu, by rw [hd, T.edge_edge]⟩)
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hv, hu, by rw [hd, tri_fan_turn_edge T h_tri refl gen]⟩)))

theorem triEdgeDart_step (T : Hypermap) (refl : Bool) (gen : T.Dart)
    {x y z u v w : Nat} {d : T.Dart}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (htri : pureTriAdj x y z u v = w) (hw : w ≠ 63)
    (h : triEdgeDart T refl gen x y z u v = some d) :
    triEdgeDart T refl gen x y z u w = some ((nodePermOriented T refl).f d) := by
  dsimp only [pureTriAdj] at htri
  simp only [Bool.and_eq_true, beq_iff_eq] at htri
  rw [triEdgeDart_eq_some_iff hxy hyz hxz] at h ⊢
  rcases h with ⟨hu, hv, hd⟩ | ⟨hu, hv, hd⟩ | ⟨hu, hv, hd⟩ |
                ⟨hu, hv, hd⟩ | ⟨hu, hv, hd⟩ | ⟨hu, hv, hd⟩
  · rw [hu, hv] at htri; simp at htri; subst w
    exact Or.inr (Or.inl ⟨hu, rfl, by rw [hd]⟩)
  · exfalso; rw [hu, hv] at htri
    split at htri
    · exact hyz (by omega)
    · split at htri
      · exact hxy (by omega)
      · split at htri
        · exact hxz (by omega)
        · exact hw htri.symm
  · exfalso; rw [hu, hv] at htri
    split at htri
    · exact hxy (by omega)
    · split at htri
      · exact hyz (by omega)
      · split at htri
        · exact hxz (by omega)
        · exact hw htri.symm
  · rw [hu, hv] at htri
    have hfalse1 : ¬(y = x ∧ z = y) := by omega
    simp [hfalse1] at htri; subst w
    exact Or.inr (Or.inr (Or.inl ⟨hu, rfl, by rw [hd, (nodePermOriented T refl).right_inv]⟩))
  · rw [hu, hv] at htri
    have hfalse1 : ¬(z = x ∧ x = y) := by omega
    have hfalse2 : ¬(z = y ∧ x = z) := by omega
    simp [hfalse1, hfalse2] at htri; subst w
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hu, rfl, by rw [hd]⟩))))
  · exfalso; rw [hu, hv] at htri
    split at htri
    · exact hxz (by omega)
    · split at htri
      · exact hyz (by omega)
      · split at htri
        · exact hxy (by omega)
        · exact hw htri.symm

theorem triEdgeDart_mem_pureTriAdj (T : Hypermap) (refl : Bool) (gen : T.Dart)
    {x y z u v : Nat} (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (hx : x ≠ 63) (hy : y ≠ 63) (hz : z ≠ 63)
    (hsome : (triEdgeDart T refl gen x y z u v).isSome = true) :
    pureTriAdj x y z u v ≠ 63 ∨ pureTriAdj x y z v u ≠ 63 := by
  rcases Option.isSome_iff_exists.mp hsome with ⟨d, hd⟩
  rw [triEdgeDart_eq_some_iff hxy hyz hxz] at hd
  rcases hd with ⟨hu, hv, _⟩ | ⟨hu, hv, _⟩ | ⟨hu, hv, _⟩ |
                 ⟨hu, hv, _⟩ | ⟨hu, hv, _⟩ | ⟨hu, hv, _⟩
  · left; rw [hu, hv]; simp [pureTriAdj, hz]
  · right; rw [hu, hv]; simp [pureTriAdj, hxz.symm, hyz.symm, hy]
  · right; rw [hu, hv]; simp [pureTriAdj, hz]
  · left; rw [hu, hv]; simp [pureTriAdj, hxy.symm, hx]
  · left; rw [hu, hv]; simp [pureTriAdj, hxz.symm, hyz.symm, hy]
  · right; rw [hu, hv]; simp [pureTriAdj, hxy.symm, hx]

theorem triEdgeDart_sameVertex (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel) (refl : Bool) (gen : T.Dart)
    {x y z u v : Nat} {d : T.Dart}
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z)
    (h : triEdgeDart T refl gen x y z u v = some d) :
    (u = x ∧ sameVertex T d gen fuel = true) ∨
    (u = y ∧ sameVertex T d (T.edge.f gen) fuel = true) ∨
    (u = z ∧ sameVertex T d (T.edge.f ((nodePermOriented T refl).f gen)) fuel = true) := by
  rw [triEdgeDart_eq_some_iff hxy hyz hxz] at h
  rcases h with ⟨hu, _, hd⟩ | ⟨hu, _, hd⟩ | ⟨hu, _, hd⟩ |
                ⟨hu, _, hd⟩ | ⟨hu, _, hd⟩ | ⟨hu, _, hd⟩
  · exact Or.inl ⟨hu, by rw [hd]; exact sameVertex_refl T fuel gen⟩
  · exact Or.inl ⟨hu, by rw [hd]; exact sameVertex_permOriented_f T darts h_all h_len refl gen⟩
  · exact Or.inr (Or.inl ⟨hu, by rw [hd]; exact sameVertex_refl T fuel (T.edge.f gen)⟩)
  · exact Or.inr (Or.inl ⟨hu, by rw [hd]; exact sameVertex_permOriented_inv T darts h_all h_len refl (T.edge.f gen)⟩)
  · exact Or.inr (Or.inr ⟨hu, by rw [hd]; exact sameVertex_refl T fuel (T.edge.f ((nodePermOriented T refl).f gen))⟩)
  · exact Or.inr (Or.inr ⟨hu, by rw [hd]; exact sameVertex_permOriented_f T darts h_all h_len refl _⟩)

private theorem ruleRot_not_refl (T : Hypermap) (refl : Bool) (d : T.Dart) :
    ruleRot T (!refl) d = (nodePermOriented T refl).inv d := by
  cases refl <;> rfl

private theorem ruleRotInv_not_refl (T : Hypermap) (refl : Bool) (d : T.Dart) :
    ruleRotInv T (!refl) d = (nodePermOriented T refl).f d := by
  cases refl <;> rfl

private theorem cartDartOriented_zero (T : Hypermap) (deg : Nat) (refl : Bool) (d0 : T.Dart) :
    cartDartOriented T deg refl d0 0 = d0 := rfl

private theorem cartDartOriented_spoke (T : Hypermap) (deg : Nat) (refl : Bool) (d0 : T.Dart)
    {i : Nat} (hi1 : 1 ≤ i) (hideg : i ≤ deg) :
    cartDartOriented T deg refl d0 i = T.edge.f (spokeDartOriented T refl d0 i) := by
  have hi0 : (i == 0) = false := beq_false_of_ne (by omega)
  have hdiv : (i - 1) / deg = 0 := Nat.div_eq_of_lt (by omega)
  have hmod : (i - 1) % deg + 1 = i := by
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  simp [cartDartOriented, hi0, hdiv, hmod, ruleVertexDart]

private theorem cartDartOriented_hat_eq (T : Hypermap) (deg : Nat) (refl : Bool) (d0 : T.Dart)
    {i : Nat} (hi1 : 1 ≤ i) (hideg : i ≤ deg) :
    cartDartOriented T deg refl d0 (deg + i) =
      T.edge.f ((nodePermOriented T refl).inv ((nodePermOriented T refl).inv
        (T.edge.f (spokeDartOriented T refl d0 i)))) := by
  rw [cartDartOriented_hat T deg refl d0 hi1 hideg]
  simp [ruleVertexDart, ruleRot_not_refl]

private theorem cartDartOriented_fan1_eq (T : Hypermap) (deg : Nat) (refl : Bool) (d0 : T.Dart)
    {i : Nat} (hi1 : 1 ≤ i) (hideg : i ≤ deg) :
    cartDartOriented T deg refl d0 (2 * deg + i) =
      T.edge.f (Hypermap.Perm.iter (nodePermOriented T refl) 3
        (T.edge.f (spokeDartOriented T refl d0 i))) := by
  rw [cartDartOriented_fan1 T deg refl d0 hi1 hideg]
  simp [ruleVertexDart, ruleRotInv_not_refl, Hypermap.Perm.iter]

private theorem cartDartOriented_fan2_eq (T : Hypermap) (deg : Nat) (refl : Bool) (d0 : T.Dart)
    {i : Nat} (hi1 : 1 ≤ i) (hideg : i ≤ deg) :
    cartDartOriented T deg refl d0 (3 * deg + i) =
      T.edge.f (Hypermap.Perm.iter (nodePermOriented T refl) 4
        (T.edge.f (spokeDartOriented T refl d0 i))) := by
  rw [cartDartOriented_fan2 T deg refl d0 hi1 hideg]
  simp [ruleVertexDart, ruleRotInv_not_refl, Hypermap.Perm.iter]

private theorem cartDartOriented_fan3_eq (T : Hypermap) (deg : Nat) (refl : Bool) (d0 : T.Dart)
    {i : Nat} (hi1 : 1 ≤ i) (hideg : i ≤ deg) :
    cartDartOriented T deg refl d0 (4 * deg + i) =
      T.edge.f (Hypermap.Perm.iter (nodePermOriented T refl) 5
        (T.edge.f (spokeDartOriented T refl d0 i))) := by
  rw [cartDartOriented_fan3 T deg refl d0 hi1 hideg]
  cases refl <;> simp [nodePermOriented, Perm.symm, Hypermap.Perm.iter]

private theorem perm_f_spokeDartOriented_prev (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel) (refl : Bool) (d0 : T.Dart)
    {i : Nat} (hi1 : 1 ≤ i) (hideg : i ≤ nodeDegree T d0 fuel) :
    (nodePermOriented T refl).f
        (spokeDartOriented T refl d0 (if i = 1 then nodeDegree T d0 fuel else i - 1)) =
      spokeDartOriented T refl d0 i := by
  rw [spokeDartOriented_eq_iter, spokeDartOriented_eq_iter]
  by_cases hi : i = 1
  · subst hi
    simp only [↓reduceIte, Hypermap.Perm.iter]
    have hpos : 1 ≤ nodeDegree T d0 fuel := by omega
    have hpow : (nodePermOriented T refl).f
        (Hypermap.Perm.iter (nodePermOriented T refl) (nodeDegree T d0 fuel - 1) d0) =
        Hypermap.Perm.iter (nodePermOriented T refl) (nodeDegree T d0 fuel) d0 := by
      have hsub : nodeDegree T d0 fuel - 1 + 1 = nodeDegree T d0 fuel := Nat.sub_add_cancel hpos
      rw [← hsub]; rfl
    rw [hpow]
    exact perm_iter_nodePermOriented_deg_eq_self T darts h_all h_len refl d0
  · have hi_gt : 1 < i := by omega
    simp only [hi, ↓reduceIte]
    have hsub : i - 1 - 1 + 1 = i - 1 := by omega
    rw [← hsub]; rfl

private theorem perm_iter_sub_two_eq_inv2 {E : Type} (p : Perm E) {k : Nat} (hk : 2 ≤ k) (d : E)
    (hcyc : Hypermap.Perm.iter p k d = d) :
    Hypermap.Perm.iter p (k - 2) d = p.inv (p.inv d) := by
  have hk' : k = (k - 2) + 2 := by omega
  have h1 : p.f (p.f (Hypermap.Perm.iter p (k - 2) d)) = d := by
    simpa [Hypermap.Perm.iter_add, Hypermap.Perm.iter] using
      (by rw [← Hypermap.Perm.iter_add, Nat.add_comm, ← hk']; exact hcyc :
        Hypermap.Perm.iter p 2 (Hypermap.Perm.iter p (k - 2) d) = d)
  have h2 := congrArg p.inv h1
  rw [p.left_inv] at h2
  have h3 := congrArg p.inv h2
  rw [p.left_inv] at h3
  exact h3

/-- Vertex consistency and bounds for every triangle spec in `spokeTriSpecs`. -/
theorem spokeTriSpecs_vert_match (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel)
    (h_tri : ∀ x : T.Dart, T.face.f (T.face.f (T.face.f x)) = x)
    (refl : Bool) (d0 : T.Dart) (hdeg5 : 5 ≤ nodeDegree T d0 fuel) (i : Nat)
    (hi1 : 1 ≤ i) (hideg : i ≤ nodeDegree T d0 fuel)
    {x y z : Nat} {gen : T.Dart}
    (hmem : (x, y, z, gen) ∈ spokeTriSpecs T (nodeDegree T d0 fuel) refl d0 i
      (cartDegOriented T fuel (nodeDegree T d0 fuel) refl d0 i)) :
    let deg := nodeDegree T d0 fuel
    let cd := cartDegOriented T fuel deg refl d0
    x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ x ≤ 5 * deg ∧ y ≤ 5 * deg ∧ z ≤ 5 * deg ∧
      activeCartPos deg cd x ∧ activeCartPos deg cd y ∧ activeCartPos deg cd z ∧
      sameVertex T gen (cartDartOriented T deg refl d0 x) fuel = true ∧
      sameVertex T (T.edge.f gen) (cartDartOriented T deg refl d0 y) fuel = true ∧
      sameVertex T (T.edge.f ((nodePermOriented T refl).f gen))
        (cartDartOriented T deg refl d0 z) fuel = true := by
  intro deg cd
  let P := nodePermOriented T refl
  let e := T.edge.f
  let h := if i = 1 then deg else i - 1
  let s_h := spokeDartOriented T refl d0 h
  let s_i := spokeDartOriented T refl d0 i
  let a := deg + h
  let b := deg + i
  let c := 2 * deg + i
  let d_v := 3 * deg + i
  let e_v := 4 * deg + i
  have hh1 : 1 ≤ h := by dsimp [h]; split <;> omega
  have hhdeg : h ≤ deg := by dsimp [h]; split <;> omega
  have hhi : h ≠ i := by dsimp [h]; split <;> omega
  have hPsh : P.f s_h = s_i :=
    perm_f_spokeDartOriented_prev T darts h_all h_len refl d0 hi1 hideg
  have hk_eq : cd i = nodeDegree T (e s_i) fuel := by
    dsimp [cd, cartDegOriented, deg]
    rw [cartDartOriented_spoke T deg refl d0 hi1 hideg]
  have hk_cyc : Hypermap.Perm.iter P (cd i) (e s_i) = e s_i := by
    rw [hk_eq]
    exact perm_iter_nodePermOriented_deg_eq_self T darts h_all h_len refl (e s_i)
  have act0 : activeCartPos deg cd 0 := Or.inl rfl
  have acth : activeCartPos deg cd h := Or.inr (Or.inl ⟨hh1, by omega⟩)
  have acti : activeCartPos deg cd i := Or.inr (Or.inl ⟨hi1, by omega⟩)
  have acta : activeCartPos deg cd a := Or.inr (Or.inl ⟨by omega, by omega⟩)
  have actb : activeCartPos deg cd b := Or.inr (Or.inl ⟨by omega, by omega⟩)
  have sv_sh : sameVertex T s_h (cartDartOriented T deg refl d0 0) fuel = true := by
    dsimp only [s_h]
    rw [cartDartOriented_zero, spokeDartOriented_eq_iter]
    exact sameVertex_iter_permOriented T darts h_all h_len refl _ d0
  have sv_eh : sameVertex T (e s_h) (cartDartOriented T deg refl d0 h) fuel = true := by
    rw [cartDartOriented_spoke T deg refl d0 hh1 hhdeg]; exact sameVertex_refl T fuel _
  have sv_ei : sameVertex T (e s_i) (cartDartOriented T deg refl d0 i) fuel = true := by
    rw [cartDartOriented_spoke T deg refl d0 hi1 hideg]; exact sameVertex_refl T fuel _
  have sv_d1x : sameVertex T (P.f (e s_i)) (cartDartOriented T deg refl d0 i) fuel = true :=
    sameVertex_trans_of_complete T darts h_all h_len
      (sameVertex_permOriented_f T darts h_all h_len refl _) sv_ei
  have hed1 : e (P.f (e s_i)) = P.inv (e s_h) := by
    have hsi : e s_i = e (P.f s_h) := by rw [hPsh]
    rw [hsi]
    exact tri_fan_turn_edge T h_tri refl s_h
  have sv_d1y : sameVertex T (e (P.f (e s_i))) (cartDartOriented T deg refl d0 h) fuel = true := by
    rw [hed1]
    exact sameVertex_trans_of_complete T darts h_all h_len
      (sameVertex_permOriented_inv T darts h_all h_len refl _) sv_eh
  have sv_d1z : sameVertex T (e (P.f (P.f (e s_i)))) (cartDartOriented T deg refl d0 a) fuel = true := by
    have ha_dart : cartDartOriented T deg refl d0 a = e (P.inv (e (P.f (e s_i)))) := by
      rw [cartDartOriented_hat_eq T deg refl d0 hh1 hhdeg, hed1]
    have hft : e (P.inv (e (P.f (e s_i)))) = P.f (e (P.f (P.f (e s_i)))) :=
      tri_fan_turn T h_tri refl (P.f (e s_i))
    have hinv : sameVertex T (e (P.f (P.f (e s_i)))) (P.f (e (P.f (P.f (e s_i))))) fuel = true := by
      rw [sameVertex_symm_of_complete T darts h_all h_len]
      exact sameVertex_permOriented_f T darts h_all h_len refl _
    rw [ha_dart, hft]; exact hinv
  have sv_d2_base : ∀ r, sameVertex T (Hypermap.Perm.iter P r (e s_i))
      (cartDartOriented T deg refl d0 i) fuel = true := fun r =>
    sameVertex_trans_of_complete T darts h_all h_len
      (sameVertex_iter_permOriented T darts h_all h_len refl r _) sv_ei
  have sv_d2_a : sameVertex T (e (Hypermap.Perm.iter P 2 (e s_i)))
      (cartDartOriented T deg refl d0 a) fuel = true := by
    simpa [Hypermap.Perm.iter] using sv_d1z
  have sv_d3_c : sameVertex T (e (Hypermap.Perm.iter P 3 (e s_i)))
      (cartDartOriented T deg refl d0 c) fuel = true := by
    rw [cartDartOriented_fan1_eq T deg refl d0 hi1 hideg]; exact sameVertex_refl T fuel _
  have sv_d4_d : sameVertex T (e (Hypermap.Perm.iter P 4 (e s_i)))
      (cartDartOriented T deg refl d0 d_v) fuel = true := by
    rw [cartDartOriented_fan2_eq T deg refl d0 hi1 hideg]; exact sameVertex_refl T fuel _
  have sv_d5_e : sameVertex T (e (Hypermap.Perm.iter P 5 (e s_i)))
      (cartDartOriented T deg refl d0 e_v) fuel = true := by
    rw [cartDartOriented_fan3_eq T deg refl d0 hi1 hideg]; exact sameVertex_refl T fuel _
  have sv_b_last : ∀ (kval : Nat), kval = cd i → 5 ≤ kval →
      sameVertex T (e (P.f (Hypermap.Perm.iter P (kval - 3) (e s_i))))
        (cartDartOriented T deg refl d0 b) fuel = true := by
    intro kval hkval hk5
    have hstep : P.f (Hypermap.Perm.iter P (kval - 3) (e s_i)) =
        Hypermap.Perm.iter P (kval - 2) (e s_i) := by
      have hk3 : (kval - 3) + 1 = kval - 2 := by omega
      rw [← hk3]; rfl
    dsimp only [e, P]
    rw [hstep, perm_iter_sub_two_eq_inv2 (nodePermOriented T refl) (by omega) (T.edge.f s_i) (hkval ▸ hk_cyc),
        ← cartDartOriented_hat_eq T deg refl d0 hi1 hideg]
    exact sameVertex_refl T fuel _
  have hmem_base : (x, y, z, gen) ∈ [(0, h, i, s_h), (i, h, a, P.f (e s_i))] →
      x ≠ y ∧ y ≠ z ∧ x ≠ z ∧ x ≤ 5 * deg ∧ y ≤ 5 * deg ∧ z ≤ 5 * deg ∧
        activeCartPos deg cd x ∧ activeCartPos deg cd y ∧ activeCartPos deg cd z ∧
        sameVertex T gen (cartDartOriented T deg refl d0 x) fuel = true ∧
        sameVertex T (e gen) (cartDartOriented T deg refl d0 y) fuel = true ∧
        sameVertex T (e (P.f gen)) (cartDartOriented T deg refl d0 z) fuel = true := by
    intro hb
    simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hb
    rcases hb with ⟨hx, hy, hz, hgen⟩ | ⟨hx, hy, hz, hgen⟩
    · rw [hx, hy, hz, hgen]
      refine ⟨by omega, hhi, by omega, by omega, by omega, by omega, act0, acth, acti, sv_sh, sv_eh, ?_⟩
      simpa [P, hPsh] using sv_ei
    · rw [hx, hy, hz, hgen]
      exact ⟨hhi.symm, by omega, by omega, by omega, by omega, by omega, acti, acth, acta,
        sv_d1x, sv_d1y, sv_d1z⟩
  change (x, y, z, gen) ∈ spokeTriSpecs T deg refl d0 i (cd i) at hmem
  unfold spokeTriSpecs at hmem
  by_cases h5 : cd i = 5
  · rw [if_pos h5, List.mem_append] at hmem
    rcases hmem with hb | ht
    · exact hmem_base hb
    · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ht
      rcases ht with ⟨hx, hy, hz, hgen⟩
      rw [hx, hy, hz, hgen]
      exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, acti, acta, actb,
        sv_d2_base 2, sv_d2_a, sv_b_last 5 h5.symm (by omega)⟩
  · rw [if_neg h5] at hmem
    by_cases h6 : cd i = 6
    · rw [if_pos h6, List.mem_append] at hmem
      have actc : activeCartPos deg cd c :=
        Or.inr (Or.inr ⟨i, 2, hi1, hideg, Or.inl rfl, rfl, by omega, by omega⟩)
      rcases hmem with hb | ht
      · exact hmem_base hb
      · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ht
        rcases ht with ⟨hx, hy, hz, hgen⟩ | ⟨hx, hy, hz, hgen⟩
        · rw [hx, hy, hz, hgen]
          exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, acti, acta, actc,
            sv_d2_base 2, sv_d2_a, sv_d3_c⟩
        · rw [hx, hy, hz, hgen]
          exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, acti, actc, actb,
            sv_d2_base 3, sv_d3_c, sv_b_last 6 h6.symm (by omega)⟩
    · rw [if_neg h6] at hmem
      by_cases h7 : cd i = 7
      · rw [if_pos h7, List.mem_append] at hmem
        have actc : activeCartPos deg cd c :=
          Or.inr (Or.inr ⟨i, 2, hi1, hideg, Or.inl rfl, rfl, by omega, by omega⟩)
        have actd : activeCartPos deg cd d_v :=
          Or.inr (Or.inr ⟨i, 3, hi1, hideg, Or.inr (Or.inl rfl), rfl, by omega, by omega⟩)
        rcases hmem with hb | ht
        · exact hmem_base hb
        · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ht
          rcases ht with ⟨hx, hy, hz, hgen⟩ | ⟨hx, hy, hz, hgen⟩ | ⟨hx, hy, hz, hgen⟩
          · rw [hx, hy, hz, hgen]
            exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, acti, acta, actc,
              sv_d2_base 2, sv_d2_a, sv_d3_c⟩
          · rw [hx, hy, hz, hgen]
            exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, acti, actc, actd,
              sv_d2_base 3, sv_d3_c, sv_d4_d⟩
          · rw [hx, hy, hz, hgen]
            exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, acti, actd, actb,
              sv_d2_base 4, sv_d4_d, sv_b_last 7 h7.symm (by omega)⟩
      · rw [if_neg h7] at hmem
        by_cases h8 : cd i = 8
        · rw [if_pos h8, List.mem_append] at hmem
          have actc : activeCartPos deg cd c :=
            Or.inr (Or.inr ⟨i, 2, hi1, hideg, Or.inl rfl, rfl, by omega, by omega⟩)
          have actd : activeCartPos deg cd d_v :=
            Or.inr (Or.inr ⟨i, 3, hi1, hideg, Or.inr (Or.inl rfl), rfl, by omega, by omega⟩)
          have acte : activeCartPos deg cd e_v :=
            Or.inr (Or.inr ⟨i, 4, hi1, hideg, Or.inr (Or.inr rfl), rfl, by omega, by omega⟩)
          rcases hmem with hb | ht
          · exact hmem_base hb
          · simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at ht
            rcases ht with ⟨hx, hy, hz, hgen⟩ | ⟨hx, hy, hz, hgen⟩ |
                           ⟨hx, hy, hz, hgen⟩ | ⟨hx, hy, hz, hgen⟩
            · rw [hx, hy, hz, hgen]
              exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, acti, acta, actc,
                sv_d2_base 2, sv_d2_a, sv_d3_c⟩
            · rw [hx, hy, hz, hgen]
              exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, acti, actc, actd,
                sv_d2_base 3, sv_d3_c, sv_d4_d⟩
            · rw [hx, hy, hz, hgen]
              exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, acti, actd, acte,
                sv_d2_base 4, sv_d4_d, sv_d5_e⟩
            · rw [hx, hy, hz, hgen]
              exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, acti, acte, actb,
                sv_d2_base 5, sv_d5_e, sv_b_last 8 h8.symm (by omega)⟩
        · rw [if_neg h8] at hmem
          exact hmem_base hmem

private theorem list_findSome_eq_some {α β : Type} (l : List α) (f : α → Option β) {b : β}
    (h : l.findSome? f = some b) : ∃ a ∈ l, f a = some b := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
      simp only [List.findSome?] at h
      cases hfx : f x with
      | none =>
          rw [hfx] at h
          rcases ih h with ⟨a, ha, hfa⟩
          exact ⟨a, List.mem_cons_of_mem x ha, hfa⟩
      | some v =>
          rw [hfx] at h
          injection h with hvb
          exact ⟨x, List.mem_cons_self, hvb ▸ hfx⟩

private theorem list_findSome_isSome_of_mem {α β : Type} (l : List α) (f : α → Option β)
    {a : α} (ha : a ∈ l) (hfa : (f a).isSome = true) : (l.findSome? f).isSome = true := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
      simp only [List.findSome?]
      cases hfx : f x with
      | some v => rfl
      | none =>
          rcases List.mem_cons.mp ha with rfl | hmem
          · rw [hfx] at hfa; cases hfa
          · exact ih hmem

theorem spokeEdgeDart_spec (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel)
    (h_tri : ∀ x : T.Dart, T.face.f (T.face.f (T.face.f x)) = x)
    (refl : Bool) (d0 : T.Dart) (hdeg5 : 5 ≤ nodeDegree T d0 fuel)
    {i u v : Nat} (hi1 : 1 ≤ i) (hideg : i ≤ nodeDegree T d0 fuel) {d : T.Dart}
    (h : spokeEdgeDart T (nodeDegree T d0 fuel) refl d0 i
      (cartDegOriented T fuel (nodeDegree T d0 fuel) refl d0 i) u v = some d) :
    let deg := nodeDegree T d0 fuel
    let cd := cartDegOriented T fuel deg refl d0
    u ≠ v ∧ u ≤ 5 * deg ∧ v ≤ 5 * deg ∧
      activeCartPos deg cd u ∧ activeCartPos deg cd v ∧
      sameVertex T d (cartDartOriented T deg refl d0 u) fuel = true ∧
      sameVertex T (T.edge.f d) (cartDartOriented T deg refl d0 v) fuel = true := by
  intro deg cd
  rcases list_findSome_eq_some _ _ h with ⟨⟨x, y, z, gen⟩, hmem, htri⟩
  have hm := spokeTriSpecs_vert_match T darts h_all h_len h_tri refl d0 hdeg5 i hi1 hideg hmem
  rcases hm with ⟨hxy, hyz, hxz, hx5, hy5, hz5, actx, acty, actz, svx, svy, svz⟩
  have heq := (triEdgeDart_eq_some_iff hxy hyz hxz).mp htri
  have hedge := triEdgeDart_edge T h_tri refl gen hxy hyz hxz htri
  have hsvu := triEdgeDart_sameVertex T darts h_all h_len refl gen hxy hyz hxz htri
  have hsvv := triEdgeDart_sameVertex T darts h_all h_len refl gen hxy hyz hxz hedge
  have hu_case : (u = x ∧ v = y) ∨ (u = x ∧ v = z) ∨ (u = y ∧ v = x) ∨
      (u = y ∧ v = z) ∨ (u = z ∧ v = x) ∨ (u = z ∧ v = y) := by
    rcases heq with ⟨hu, hv, _⟩ | ⟨hu, hv, _⟩ | ⟨hu, hv, _⟩ |
                  ⟨hu, hv, _⟩ | ⟨hu, hv, _⟩ | ⟨hu, hv, _⟩
    · exact Or.inl ⟨hu, hv⟩
    · exact Or.inr (Or.inl ⟨hu, hv⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨hu, hv⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, hv⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hu, hv⟩))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hu, hv⟩))))
  have svu : sameVertex T d (cartDartOriented T deg refl d0 u) fuel = true := by
    rcases hsvu with ⟨rfl, hdu⟩ | ⟨rfl, hdu⟩ | ⟨rfl, hdu⟩
    · exact sameVertex_trans_of_complete T darts h_all h_len hdu svx
    · exact sameVertex_trans_of_complete T darts h_all h_len hdu svy
    · exact sameVertex_trans_of_complete T darts h_all h_len hdu svz
  have svv : sameVertex T (T.edge.f d) (cartDartOriented T deg refl d0 v) fuel = true := by
    rcases hsvv with ⟨rfl, hdv⟩ | ⟨rfl, hdv⟩ | ⟨rfl, hdv⟩
    · exact sameVertex_trans_of_complete T darts h_all h_len hdv svx
    · exact sameVertex_trans_of_complete T darts h_all h_len hdv svy
    · exact sameVertex_trans_of_complete T darts h_all h_len hdv svz
  rcases hu_case with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨hxy, hx5, hy5, actx, acty, svu, svv⟩
  · exact ⟨hxz, hx5, hz5, actx, actz, svu, svv⟩
  · exact ⟨hxy.symm, hy5, hx5, acty, actx, svu, svv⟩
  · exact ⟨hyz, hy5, hz5, acty, actz, svu, svv⟩
  · exact ⟨hxz.symm, hz5, hx5, actz, actx, svu, svv⟩
  · exact ⟨hyz.symm, hz5, hy5, actz, acty, svu, svv⟩

theorem spokeEdgeDart_eq_canonCartDart (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel)
    (h_tri : ∀ x : T.Dart, T.face.f (T.face.f (T.face.f x)) = x)
    (refl : Bool) (d0 : T.Dart) (hdeg5 : 5 ≤ nodeDegree T d0 fuel)
    (hcw : CartwheelEmbedded T fuel refl d0)
    {i u v : Nat} (hi1 : 1 ≤ i) (hideg : i ≤ nodeDegree T d0 fuel) {d : T.Dart}
    (h : spokeEdgeDart T (nodeDegree T d0 fuel) refl d0 i
      (cartDegOriented T fuel (nodeDegree T d0 fuel) refl d0 i) u v = some d) :
    canonCartDart T (nodeDegree T d0 fuel) refl d0
      (cartDegOriented T fuel (nodeDegree T d0 fuel) refl d0) u v = d := by
  let deg := nodeDegree T d0 fuel
  let cd := cartDegOriented T fuel deg refl d0
  have himem : i ∈ List.range' 1 deg := List.mem_range'.mpr ⟨i - 1, by omega, by omega⟩
  have hsome : ((List.range' 1 deg).findSome?
      (fun j => spokeEdgeDart T deg refl d0 j (cd j) u v)).isSome = true :=
    list_findSome_isSome_of_mem _ _ himem (by rw [h]; rfl)
  rcases Option.isSome_iff_exists.mp hsome with ⟨d', hd'⟩
  rcases list_findSome_eq_some _ _ hd' with ⟨j, hjmem, hj_eq⟩
  have hj_range := List.mem_range'.mp hjmem
  rcases hj_range with ⟨k, hk, hk_eq⟩
  simp only [Nat.one_mul] at hk_eq
  subst hk_eq
  have hj1 : 1 ≤ 1 + k := by omega
  have hjdeg : 1 + k ≤ deg := by omega
  have sp_i := spokeEdgeDart_spec T darts h_all h_len h_tri refl d0 hdeg5 hi1 hideg h
  have sp_j := spokeEdgeDart_spec T darts h_all h_len h_tri refl d0 hdeg5 hj1 hjdeg hj_eq
  have heq : d' = d :=
    hcw.2.2 u v sp_i.2.2.2.1 sp_i.2.2.2.2.1 sp_i.1 d' d
      sp_j.2.2.2.2.2.1 sp_i.2.2.2.2.2.1 sp_j.2.2.2.2.2.2 sp_i.2.2.2.2.2.2
  dsimp only [canonCartDart]
  rw [hd', Option.getD_some, heq]

theorem canonCartDart_edge_of_spokeSome (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel)
    (h_tri : ∀ x : T.Dart, T.face.f (T.face.f (T.face.f x)) = x)
    (refl : Bool) (d0 : T.Dart) (hdeg5 : 5 ≤ nodeDegree T d0 fuel)
    (hcw : CartwheelEmbedded T fuel refl d0)
    {i u v : Nat} (hi1 : 1 ≤ i) (hideg : i ≤ nodeDegree T d0 fuel)
    (hsome : (spokeEdgeDart T (nodeDegree T d0 fuel) refl d0 i
      (cartDegOriented T fuel (nodeDegree T d0 fuel) refl d0 i) u v).isSome = true) :
    let deg := nodeDegree T d0 fuel
    let cd := cartDegOriented T fuel deg refl d0
    u ≠ v ∧ u ≤ 5 * deg ∧ v ≤ 5 * deg ∧
      activeCartPos deg cd u ∧ activeCartPos deg cd v ∧
      sameVertex T (canonCartDart T deg refl d0 cd u v) (cartDartOriented T deg refl d0 u) fuel = true ∧
      sameVertex T (T.edge.f (canonCartDart T deg refl d0 cd u v))
        (cartDartOriented T deg refl d0 v) fuel = true ∧
      T.edge.f (canonCartDart T deg refl d0 cd u v) = canonCartDart T deg refl d0 cd v u := by
  intro deg cd
  rcases Option.isSome_iff_exists.mp hsome with ⟨d, hd⟩
  rcases list_findSome_eq_some _ _ hd with ⟨⟨x, y, z, gen⟩, hmem, htri⟩
  have hm := spokeTriSpecs_vert_match T darts h_all h_len h_tri refl d0 hdeg5 i hi1 hideg hmem
  have hedge : triEdgeDart T refl gen x y z v u = some (T.edge.f d) :=
    triEdgeDart_edge T h_tri refl gen hm.1 hm.2.1 hm.2.2.1 htri
  have hvu_some : (spokeEdgeDart T deg refl d0 i (cd i) v u).isSome = true :=
    list_findSome_isSome_of_mem _ _ hmem (by dsimp; rw [hedge]; rfl)
  rcases Option.isSome_iff_exists.mp hvu_some with ⟨d', hd'⟩
  have sp_uv := spokeEdgeDart_spec T darts h_all h_len h_tri refl d0 hdeg5 hi1 hideg hd
  have sp_vu := spokeEdgeDart_spec T darts h_all h_len h_tri refl d0 hdeg5 hi1 hideg hd'
  have hc_uv := spokeEdgeDart_eq_canonCartDart T darts h_all h_len h_tri refl d0 hdeg5 hcw hi1 hideg hd
  have hc_vu := spokeEdgeDart_eq_canonCartDart T darts h_all h_len h_tri refl d0 hdeg5 hcw hi1 hideg hd'
  have hdd' : T.edge.f d = d' :=
    hcw.2.2 v u sp_vu.2.2.2.1 sp_vu.2.2.2.2.1 sp_vu.1 (T.edge.f d) d'
      sp_uv.2.2.2.2.2.2 sp_vu.2.2.2.2.2.1
      (by rw [T.edge_edge]; exact sp_uv.2.2.2.2.2.1) sp_vu.2.2.2.2.2.2
  refine ⟨sp_uv.1, sp_uv.2.1, sp_uv.2.2.1, sp_uv.2.2.2.1, sp_uv.2.2.2.2.1, ?_, ?_, ?_⟩
  · rw [hc_uv]; exact sp_uv.2.2.2.2.2.1
  · rw [hc_uv]; exact sp_uv.2.2.2.2.2.2
  · rw [hc_uv, hc_vu, hdd']

theorem canonCartDart_step_of_tri (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel)
    (h_tri : ∀ x : T.Dart, T.face.f (T.face.f (T.face.f x)) = x)
    (refl : Bool) (d0 : T.Dart) (hdeg5 : 5 ≤ nodeDegree T d0 fuel)
    (hcw : CartwheelEmbedded T fuel refl d0)
    {i x y z u v w : Nat} {gen : T.Dart}
    (hi1 : 1 ≤ i) (hideg : i ≤ nodeDegree T d0 fuel)
    (hmem : (x, y, z, gen) ∈ spokeTriSpecs T (nodeDegree T d0 fuel) refl d0 i
      (cartDegOriented T fuel (nodeDegree T d0 fuel) refl d0 i))
    (htri : pureTriAdj x y z u v = w) (hw : w ≠ 63) :
    let deg := nodeDegree T d0 fuel
    let cd := cartDegOriented T fuel deg refl d0
    (spokeEdgeDart T deg refl d0 i (cd i) u v).isSome = true ∧
      (spokeEdgeDart T deg refl d0 i (cd i) u w).isSome = true ∧
      canonCartDart T deg refl d0 cd u w =
        (nodePermOriented T refl).f (canonCartDart T deg refl d0 cd u v) := by
  intro deg cd
  have hm := spokeTriSpecs_vert_match T darts h_all h_len h_tri refl d0 hdeg5 i hi1 hideg hmem
  dsimp only [pureTriAdj] at htri
  simp only [Bool.and_eq_true, beq_iff_eq] at htri
  have hpair : ∃ d, triEdgeDart T refl gen x y z u v = some d := by
    split at htri
    · rename_i h1; exact ⟨gen, by rw [triEdgeDart_eq_some_iff hm.1 hm.2.1 hm.2.2.1]; exact Or.inl ⟨h1.1, h1.2, rfl⟩⟩
    · split at htri
      · rename_i h2; exact ⟨(nodePermOriented T refl).inv (T.edge.f gen),
          by rw [triEdgeDart_eq_some_iff hm.1 hm.2.1 hm.2.2.1]; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h2.1, h2.2, rfl⟩)))⟩
      · split at htri
        · rename_i h3; exact ⟨T.edge.f ((nodePermOriented T refl).f gen),
            by rw [triEdgeDart_eq_some_iff hm.1 hm.2.1 hm.2.2.1]; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h3.1, h3.2, rfl⟩))))⟩
        · exact absurd htri.symm hw
  rcases hpair with ⟨d, hd⟩
  have hw_step := triEdgeDart_step T refl gen hm.1 hm.2.1 hm.2.2.1 (by
    dsimp only [pureTriAdj]; simp only [Bool.and_eq_true, beq_iff_eq]; exact htri) hw hd
  have huv_some : (spokeEdgeDart T deg refl d0 i (cd i) u v).isSome = true :=
    list_findSome_isSome_of_mem _ _ hmem (by dsimp; rw [hd]; rfl)
  have huw_some : (spokeEdgeDart T deg refl d0 i (cd i) u w).isSome = true :=
    list_findSome_isSome_of_mem _ _ hmem (by dsimp; rw [hw_step]; rfl)
  rcases Option.isSome_iff_exists.mp huv_some with ⟨d_uv, hd_uv⟩
  rcases Option.isSome_iff_exists.mp huw_some with ⟨d_uw, hd_uw⟩
  have sp_uv := spokeEdgeDart_spec T darts h_all h_len h_tri refl d0 hdeg5 hi1 hideg hd_uv
  have sp_uw := spokeEdgeDart_spec T darts h_all h_len h_tri refl d0 hdeg5 hi1 hideg hd_uw
  have hc_uv := spokeEdgeDart_eq_canonCartDart T darts h_all h_len h_tri refl d0 hdeg5 hcw hi1 hideg hd_uv
  have hc_uw := spokeEdgeDart_eq_canonCartDart T darts h_all h_len h_tri refl d0 hdeg5 hcw hi1 hideg hd_uw
  have sv_x := spokeTriSpecs_vert_match T darts h_all h_len h_tri refl d0 hdeg5 i hi1 hideg hmem
  have hedge_d := triEdgeDart_edge T h_tri refl gen hm.1 hm.2.1 hm.2.2.1 hd
  have hedge_dw := triEdgeDart_edge T h_tri refl gen hm.1 hm.2.1 hm.2.2.1 hw_step
  have d_same_u : sameVertex T d (cartDartOriented T deg refl d0 u) fuel = true := by
    rcases triEdgeDart_sameVertex T darts h_all h_len refl gen hm.1 hm.2.1 hm.2.2.1 hd with
      ⟨rfl, hdu⟩ | ⟨rfl, hdu⟩ | ⟨rfl, hdu⟩
    · exact sameVertex_trans_of_complete T darts h_all h_len hdu sv_x.2.2.2.2.2.2.2.2.2.1
    · exact sameVertex_trans_of_complete T darts h_all h_len hdu sv_x.2.2.2.2.2.2.2.2.2.2.1
    · exact sameVertex_trans_of_complete T darts h_all h_len hdu sv_x.2.2.2.2.2.2.2.2.2.2.2
  have d_same_v : sameVertex T (T.edge.f d) (cartDartOriented T deg refl d0 v) fuel = true := by
    rcases triEdgeDart_sameVertex T darts h_all h_len refl gen hm.1 hm.2.1 hm.2.2.1 hedge_d with
      ⟨rfl, hdv⟩ | ⟨rfl, hdv⟩ | ⟨rfl, hdv⟩
    · exact sameVertex_trans_of_complete T darts h_all h_len hdv sv_x.2.2.2.2.2.2.2.2.2.1
    · exact sameVertex_trans_of_complete T darts h_all h_len hdv sv_x.2.2.2.2.2.2.2.2.2.2.1
    · exact sameVertex_trans_of_complete T darts h_all h_len hdv sv_x.2.2.2.2.2.2.2.2.2.2.2
  have dw_same_w : sameVertex T (T.edge.f ((nodePermOriented T refl).f d))
      (cartDartOriented T deg refl d0 w) fuel = true := by
    rcases triEdgeDart_sameVertex T darts h_all h_len refl gen hm.1 hm.2.1 hm.2.2.1 hedge_dw with
      ⟨rfl, hdw⟩ | ⟨rfl, hdw⟩ | ⟨rfl, hdw⟩
    · exact sameVertex_trans_of_complete T darts h_all h_len hdw sv_x.2.2.2.2.2.2.2.2.2.1
    · exact sameVertex_trans_of_complete T darts h_all h_len hdw sv_x.2.2.2.2.2.2.2.2.2.2.1
    · exact sameVertex_trans_of_complete T darts h_all h_len hdw sv_x.2.2.2.2.2.2.2.2.2.2.2
  have hd_eq : d_uv = d :=
    hcw.2.2 u v sp_uv.2.2.2.1 sp_uv.2.2.2.2.1 sp_uv.1 d_uv d
      sp_uv.2.2.2.2.2.1 d_same_u sp_uv.2.2.2.2.2.2 d_same_v
  have hdw_eq : d_uw = (nodePermOriented T refl).f d :=
    hcw.2.2 u w sp_uw.2.2.2.1 sp_uw.2.2.2.2.1 sp_uw.1 d_uw ((nodePermOriented T refl).f d)
      sp_uw.2.2.2.2.2.1
      (sameVertex_trans_of_complete T darts h_all h_len
        (sameVertex_permOriented_f T darts h_all h_len refl d) d_same_u)
      sp_uw.2.2.2.2.2.2 dw_same_w
  refine ⟨huv_some, huw_some, ?_⟩
  rw [hc_uw, hc_uv, hdw_eq, hd_eq]

end CartwheelCanonicalDarts

section SWARAndIsoSoundness

private theorem testBit_land_eq (a b i : Nat) :
    (a.land b).testBit i = (a.testBit i && b.testBit i) := by
  change (a &&& b).testBit i = _; exact Nat.testBit_and a b i

private theorem testBit_lor_eq (a b i : Nat) :
    (a.lor b).testBit i = (a.testBit i || b.testBit i) := by
  change (a ||| b).testBit i = _; exact Nat.testBit_or a b i

private theorem testBit_xor_eq (a b i : Nat) :
    (a.xor b).testBit i = xor (a.testBit i) (b.testBit i) := by
  change (a ^^^ b).testBit i = _; exact Nat.testBit_xor a b i

private theorem testBit_shiftLeft_eq (a s i : Nat) :
    (a.shiftLeft s).testBit i = (decide (i ≥ s) && a.testBit (i - s)) := by
  change (a <<< s).testBit i = _; exact Nat.testBit_shiftLeft (x := a)

private theorem testBit_shiftRight_eq (a s i : Nat) :
    (a.shiftRight s).testBit i = a.testBit (s + i) := by
  change (a >>> s).testBit i = _; exact Nat.testBit_shiftRight (x := a)

private theorem sixThree_eq : (63 : Nat) = 2 ^ 6 - 1 := by decide
private theorem one_eq_two_pow_zero : (1 : Nat) = 2 ^ 0 := by decide
private theorem emptyImgNat_eq : emptyImgNat = 2 ^ 180 - 1 := by decide
private theorem all63Nat_eq_split :
    all63Nat = Nat.lor (2 ^ 180 - 1) (Nat.shiftLeft (2 ^ 180 - 1) 180) := by decide

private theorem testBit_63 (b : Nat) : (63 : Nat).testBit b = decide (b < 6) := by
  rw [sixThree_eq, Nat.testBit_two_pow_sub_one]

private theorem testBit_emptyImgNat (k : Nat) (hk : k < 180) :
    emptyImgNat.testBit k = true := by
  rw [emptyImgNat_eq, Nat.testBit_two_pow_sub_one]; simp [hk]

private theorem testBit_all63Nat (k : Nat) (hk : k < 360) :
    all63Nat.testBit k = true := by
  rw [all63Nat_eq_split, testBit_lor_eq, testBit_shiftLeft_eq]
  rw [Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow_sub_one]
  by_cases h180 : k < 180
  · simp [h180]
  · have hge : k ≥ 180 := Nat.le_of_not_lt h180
    have hlt : k - 180 < 180 := by omega
    simp [hge, hlt]

private theorem getImgNat_lt_64 (img u : Nat) : getImgNat img u < 64 := by
  unfold getImgNat
  change (img >>> (u.mul 6)) &&& 63 < 2 ^ 6
  exact Nat.and_lt_two_pow _ (by decide)

private theorem getLaneNat_lt_64 (st p : Nat) : getLaneNat st p < 64 := by
  unfold getLaneNat
  change (st >>> (p.mul 6)) &&& 63 < 2 ^ 6
  exact Nat.and_lt_two_pow _ (by decide)

private theorem testBit_64_pow (x b : Nat) (hx : x < 64) (hb : ¬ b < 6) :
    x.testBit b = false := by
  have hpow : 64 ≤ 2 ^ b := by
    calc (64 : Nat) = 2 ^ 6 := by decide
      _ ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) (Nat.le_of_not_lt hb)
  exact Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hx hpow)

private theorem getLaneNat_zero (p : Nat) : getLaneNat 0 p = 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  unfold getLaneNat
  rw [testBit_land_eq, testBit_shiftRight_eq]
  simp

private theorem strictNat_eq {α : Type} (n : Nat) (k : Nat → α) : strictNat n k = k n := by
  cases n <;> rfl

private theorem bool_rec_eq {α : Type} (f t : α) (b : Bool) :
    Bool.rec f t b = if b = true then t else f := by
  cases b <;> rfl

private theorem getLaneNat_setLaneNat_eq (st p val : Nat) (hp : p < 60) :
    getLaneNat (setLaneNat st p val) p = val.land 63 := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 6
  · unfold getLaneNat setLaneNat
    simp only [Nat.mul_eq, testBit_land_eq, testBit_lor_eq, testBit_xor_eq,
      testBit_shiftRight_eq, testBit_shiftLeft_eq, testBit_63]
    have hall : all63Nat.testBit (p * 6 + b) = true := testBit_all63Nat (p * 6 + b) (by omega)
    have hge : p * 6 + b ≥ p * 6 := Nat.le_add_right _ _
    have hsub : p * 6 + b - p * 6 = b := Nat.add_sub_cancel_left _ _
    simp [hb, hall, hge, hsub]
  · have h2 : val.land 63 < 64 := by
      change val &&& 63 < 2 ^ 6; exact Nat.and_lt_two_pow _ (by decide)
    rw [testBit_64_pow _ b (getLaneNat_lt_64 _ _) hb, testBit_64_pow _ b h2 hb]

private theorem getLaneNat_setLaneNat_ne (st p q val : Nat) (_hp : p < 60) (hq : q < 60)
    (hne : q ≠ p) : getLaneNat (setLaneNat st p val) q = getLaneNat st q := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b < 6
  · unfold getLaneNat setLaneNat
    simp only [Nat.mul_eq, testBit_land_eq, testBit_lor_eq, testBit_xor_eq,
      testBit_shiftRight_eq, testBit_shiftLeft_eq, testBit_63]
    have hall : all63Nat.testBit (q * 6 + b) = true := testBit_all63Nat (q * 6 + b) (by omega)
    by_cases hge : q * 6 + b ≥ p * 6
    · have hge6 : ¬ (q * 6 + b - p * 6 < 6) := by omega
      simp [hb, hall, hge, hge6]
    · simp [hb, hall, hge]
  · rw [testBit_64_pow _ b (getLaneNat_lt_64 _ _) hb,
      testBit_64_pow _ b (getLaneNat_lt_64 _ _) hb]

private theorem shiftRight_land_one_eq_ite (m p : Nat) :
    (m.shiftRight p).land 1 = if m.testBit p then 1 else 0 := by
  apply Nat.eq_of_testBit_eq
  intro b
  by_cases hb : b = 0
  · subst hb
    rw [testBit_land_eq, testBit_shiftRight_eq]
    cases hm : m.testBit p <;> simp [hm]
  · have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb
    have hpow : 2 ≤ 2 ^ b := by
      calc (2 : Nat) = 2 ^ 1 := by decide
        _ ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) hb1
    have hlhs : (m.shiftRight p).land 1 < 2 := by
      change (m >>> p) &&& 1 < 2 ^ 1; exact Nat.and_lt_two_pow _ (by decide)
    have hrhs : (if m.testBit p then (1 : Nat) else 0) < 2 := by
      cases m.testBit p <;> decide
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hlhs hpow),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hrhs hpow)]

private theorem mask_beq_zero_eq_not_testBit (m p : Nat) :
    ((m.shiftRight p).land 1).beq 0 = !m.testBit p := by
  rw [shiftRight_land_one_eq_ite]
  cases m.testBit p <;> decide

private theorem testBit_lor_shiftLeft_one (m w k : Nat) :
    (m.lor (Nat.shiftLeft 1 w)).testBit k = (decide (k = w) || m.testBit k) := by
  rw [testBit_lor_eq, testBit_shiftLeft_eq]
  by_cases hkw : k = w
  · subst hkw; simp
  · by_cases hge : k ≥ w
    · have hne0 : k - w ≠ 0 := by omega
      have htb : (1 : Nat).testBit (k - w) = false :=
        Nat.testBit_lt_two_pow (by
          calc (1 : Nat) < 2 ^ 1 := by decide
            _ ≤ 2 ^ (k - w) := Nat.pow_le_pow_right (by decide) (by omega))
      simp [hkw, hge, htb]
    · simp [hkw, hge]

private def maskExactDeg (m : Nat) : Nat :=
  if m.beq 1 then 5 else if m.beq 2 then 6 else if m.beq 4 then 7 else if m.beq 8 then 8 else 0

private theorem getUppStrict_pos (deg st p : Nat) (hp : p ≠ 0) :
    getUppStrict deg st p = laneUpp (getLaneNat st p) := by
  have hp0 : p.beq 0 = false := by cases p with | zero => contradiction | succ _ => rfl
  unfold getUppStrict laneUpp
  rw [bool_rec_eq, hp0]
  simp only [strictNat_eq, bool_rec_eq, Bool.false_eq_true, ↓reduceIte]

private theorem getExactDegStrict_pos (deg st p : Nat) (hp : p ≠ 0) :
    getExactDegStrict deg st p = maskExactDeg (getLaneNat st p) := by
  have hp0 : p.beq 0 = false := by cases p with | zero => contradiction | succ _ => rfl
  unfold getExactDegStrict maskExactDeg
  rw [bool_rec_eq, hp0]
  simp only [strictNat_eq, bool_rec_eq, Bool.false_eq_true, ↓reduceIte]

private theorem degBitIdx_ge9 (d : Nat) (hd : 9 ≤ d) : degBitIdx d = 4 := by
  unfold degBitIdx
  have h5 : ¬ d ≤ 5 := by omega
  have h6 : (d == 6) = false := beq_false_of_ne (by omega)
  have h7 : (d == 7) = false := beq_false_of_ne (by omega)
  have h8 : (d == 8) = false := beq_false_of_ne (by omega)
  simp [h5, h6, h7, h8]

private theorem mask_bit4_false_of_laneUpp_le8 :
    ∀ m : Fin 32, laneUpp m.val ≤ 8 → m.val.testBit 4 = false := by
  decide +kernel

private theorem mask_bit4_false_of_exactDeg_ne0 :
    ∀ m : Fin 32, maskExactDeg m.val ≠ 0 → m.val.testBit 4 = false := by
  decide +kernel

private theorem lane_mask_exact_spec :
    ∀ (m : Fin 32) (d : Fin 9),
      maskExactDeg m.val ≠ 0 → m.val.testBit (degBitIdx d.val) = true → 5 ≤ d.val →
        maskExactDeg m.val = laneUpp m.val ∧ d.val = maskExactDeg m.val ∧
          5 ≤ maskExactDeg m.val ∧ maskExactDeg m.val ≤ 8 := by
  decide +kernel

private theorem lane_mask_upp5_imp_exact5 :
    ∀ (m : Fin 32) (d : Fin 9),
      laneUpp m.val = 5 → m.val.testBit (degBitIdx d.val) = true → 5 ≤ d.val →
        maskExactDeg m.val = 5 := by
  decide +kernel

private theorem lane_mask_upp_le_12 :
    ∀ (m : Fin 32), laneUpp m.val ≤ 12 := by
  decide +kernel

private theorem cartDeg_eq_exactDeg_of_ne_zero {deg : Nat} {cartDeg : Nat → Nat} {cur i : Nat}
    (hm31 : MatchesCartState31 deg cartDeg cur) (hi1 : 1 ≤ i) (hi5 : i ≤ 5 * deg)
    (hmin5 : 5 ≤ cartDeg i)
    (hex : getExactDegStrict deg cur i ≠ 0) :
    getExactDegStrict deg cur i = getUppStrict deg cur i ∧
      cartDeg i = getExactDegStrict deg cur i ∧
      5 ≤ getExactDegStrict deg cur i ∧ getExactDegStrict deg cur i ≤ 8 := by
  have hi0 : i ≠ 0 := by omega
  rw [getExactDegStrict_pos deg cur i hi0] at hex ⊢
  rw [getUppStrict_pos deg cur i hi0]
  have hm32 : getLaneNat cur i < 32 := Nat.lt_succ_of_le (hm31.2 i hi1 hi5)
  have htb := hm31.1 i hi1 hi5
  have hd_lt9 : cartDeg i < 9 := by
    apply Decidable.byContradiction
    intro hge
    have hge9 : 9 ≤ cartDeg i := Nat.le_of_not_lt hge
    rw [degBitIdx_ge9 _ hge9] at htb
    have h4 := mask_bit4_false_of_exactDeg_ne0 ⟨getLaneNat cur i, hm32⟩ hex
    rw [h4] at htb
    contradiction
  exact lane_mask_exact_spec ⟨getLaneNat cur i, hm32⟩ ⟨cartDeg i, hd_lt9⟩ hex htb hmin5

private theorem getExactDeg_eq_5_of_upp_eq_5 {deg : Nat} {cartDeg : Nat → Nat} {cur i : Nat}
    (hm31 : MatchesCartState31 deg cartDeg cur) (hi1 : 1 ≤ i) (hi5 : i ≤ 5 * deg)
    (hmin5 : 5 ≤ cartDeg i) (hupp5 : getUppStrict deg cur i = 5) :
    getExactDegStrict deg cur i = 5 := by
  have hi0 : i ≠ 0 := by omega
  rw [getExactDegStrict_pos deg cur i hi0]
  rw [getUppStrict_pos deg cur i hi0] at hupp5
  have hm32 : getLaneNat cur i < 32 := Nat.lt_succ_of_le (hm31.2 i hi1 hi5)
  have htb := hm31.1 i hi1 hi5
  have hd_lt9 : cartDeg i < 9 := by
    apply Decidable.byContradiction
    intro hge
    have hge9 : 9 ≤ cartDeg i := Nat.le_of_not_lt hge
    rw [degBitIdx_ge9 _ hge9] at htb
    have h4 := mask_bit4_false_of_laneUpp_le8 ⟨getLaneNat cur i, hm32⟩
      (by change laneUpp (getLaneNat cur i) ≤ 8; omega)
    rw [h4] at htb
    contradiction
  exact lane_mask_upp5_imp_exact5 ⟨getLaneNat cur i, hm32⟩ ⟨cartDeg i, hd_lt9⟩ hupp5 htb hmin5

private noncomputable def initIsoVertsAux (deg ring st img : Nat) (ivs : List IntVert)
    (invMap usedMask : Nat) : Option (Nat × Nat) :=
  match ivs with
  | [] => some (invMap, usedMask)
  | iv :: rest =>
    let fu := getImgNat img iv.u
    if fu.ble (5 * deg) = true then
      if (!((usedMask.shiftRight fu).land 1).beq 0) = true then none
      else if iv.d.beq (getUppStrict deg st fu) = true then
        let okFan :=
          if fu.ble (2 * deg) = true then true
          else
            let i := (fu - 1).mod deg + 1
            let ex := getExactDegStrict deg st i
            !ex.beq 0 && ((fu - 1).div deg + 4).ble ex
        if okFan = true then
          initIsoVertsAux deg ring st img rest
            (setLaneNat invMap fu (iv.u - (ring + 1)))
            (usedMask.lor (Nat.shiftLeft 1 fu))
        else none
      else none
    else none

private theorem initIsoVertsRec_eq_aux (deg ring st img : Nat) (ivs : List IntVert) :
    initIsoVertsRec deg ring st img ivs =
      initIsoVertsAux deg ring st img ivs 0 0 := by
  suffices h : ∀ invMap usedMask,
      List.rec (motive := fun _ => Nat → Nat → Option (Nat × Nat))
        (fun im um => some (im, um))
        (fun iv _ ih invMap usedMask =>
          match iv with
          | { u := ivu, d := ivd, worried := _, cyc := _ } =>
            strictNat (getImgNat img ivu) fun fu =>
              Bool.rec none
                (Bool.rec
                  (Bool.rec none
                    (have okFan :=
                      Bool.rec
                        (have i := ((fu.sub 1).mod deg).add 1;
                        strictNat (getExactDegStrict deg st i) fun ex =>
                          !ex.beq 0 && (((fu.sub 1).div deg).add 4).ble ex)
                        true (fu.ble (Nat.mul 2 deg));
                    Bool.rec none
                      (strictNat (usedMask.lor (Nat.shiftLeft 1 fu)) fun usedMask' =>
                        strictNat (setLaneNat invMap fu (ivu.sub (ring.add 1))) fun invMap' =>
                          ih invMap' usedMask')
                      okFan)
                    (ivd.beq (getUppStrict deg st fu)))
                  none !((usedMask.shiftRight fu).land 1).beq 0)
                (fu.ble (Nat.mul 5 deg)))
        ivs invMap usedMask =
        initIsoVertsAux deg ring st img ivs invMap usedMask from h 0 0
  intro invMap usedMask
  induction ivs generalizing invMap usedMask with
  | nil => rfl
  | cons iv rest ih =>
    cases iv with
    | mk ivu ivd ivw ivcyc =>
      dsimp only [initIsoVertsAux]
      simp only [strictNat_eq, bool_rec_eq, Nat.add_eq, Nat.sub_eq, Nat.mul_eq] at ih ⊢
      cases (getImgNat img ivu).ble (5 * deg) <;> simp only [Bool.false_eq_true, ↓reduceIte]
      cases !((usedMask.shiftRight (getImgNat img ivu)).land 1).beq 0 <;>
        simp only [Bool.false_eq_true, ↓reduceIte]
      cases ivd.beq (getUppStrict deg st (getImgNat img ivu)) <;>
        simp only [Bool.false_eq_true, ↓reduceIte]
      cases (if (getImgNat img ivu).ble (2 * deg) = true then true
        else !(getExactDegStrict deg st ((getImgNat img ivu - 1).mod deg + 1)).beq 0 &&
          ((getImgNat img ivu - 1).div deg + 4).ble
            (getExactDegStrict deg st ((getImgNat img ivu - 1).mod deg + 1))) <;>
        simp only [Bool.false_eq_true, ↓reduceIte]
      exact ih _ _

private theorem initIsoVertsAux_spec {deg ring st img : Nat} (hdeg11 : deg ≤ 11)
    {ivs : List IntVert} (hbnd : ∀ iv ∈ ivs, ring + 1 ≤ iv.u ∧ iv.u ≤ ring + 12)
    {invMap usedMask invFinal usedFinal : Nat}
    (hinit : initIsoVertsAux deg ring st img ivs invMap usedMask = some (invFinal, usedFinal)) :
    (∀ k, usedMask.testBit k = true → usedFinal.testBit k = true) ∧
    (∀ k, usedFinal.testBit k = true ↔
      usedMask.testBit k = true ∨ ∃ iv ∈ ivs, getImgNat img iv.u = k) ∧
    (∀ iv ∈ ivs,
      getImgNat img iv.u ≤ 5 * deg ∧
      usedMask.testBit (getImgNat img iv.u) = false ∧
      iv.d = getUppStrict deg st (getImgNat img iv.u) ∧
      (getImgNat img iv.u > 2 * deg →
        let fu := getImgNat img iv.u
        let i := (fu - 1) % deg + 1
        getExactDegStrict deg st i ≠ 0 ∧ (fu - 1) / deg + 4 ≤ getExactDegStrict deg st i) ∧
      getLaneNat invFinal (getImgNat img iv.u) = iv.u - (ring + 1)) ∧
    (∀ i j, (hi : i < ivs.length) → (hj : j < ivs.length) → i ≠ j →
      getImgNat img ivs[i].u ≠ getImgNat img ivs[j].u) := by
  induction ivs generalizing invMap usedMask with
  | nil =>
    simp only [initIsoVertsAux, Option.some.injEq, Prod.mk.injEq] at hinit
    rcases hinit with ⟨rfl, rfl⟩
    refine ⟨fun _ h => h, fun k => ⟨fun h => Or.inl h, fun h => ?_⟩, ?_, ?_⟩
    · rcases h with h | ⟨_, hmem, _⟩
      · exact h
      · simp at hmem
    · intro _ hmem; simp at hmem
    · intro _ _ hi; simp at hi
  | cons iv rest ih =>
    dsimp only [initIsoVertsAux] at hinit
    split at hinit
    · rename_i hle5
      have hfu_le : getImgNat img iv.u ≤ 5 * deg := Nat.le_of_ble_eq_true hle5
      have hfu_lt60 : getImgNat img iv.u < 60 := by omega
      split at hinit
      · simp at hinit
      · rename_i hbit0
        have hbit_false : usedMask.testBit (getImgNat img iv.u) = false := by
          rw [mask_beq_zero_eq_not_testBit] at hbit0
          cases hm : usedMask.testBit (getImgNat img iv.u)
          · rfl
          · simp [hm] at hbit0
        split at hinit
        · rename_i hd_eq
          have hivd : iv.d = getUppStrict deg st (getImgNat img iv.u) := Nat.eq_of_beq_eq_true hd_eq
          have ⟨hfan_prop, hinit_tail⟩ :
              (getImgNat img iv.u > 2 * deg →
                let fu := getImgNat img iv.u
                let i := (fu - 1) % deg + 1
                getExactDegStrict deg st i ≠ 0 ∧
                  (fu - 1) / deg + 4 ≤ getExactDegStrict deg st i) ∧
              initIsoVertsAux deg ring st img rest
                (setLaneNat invMap (getImgNat img iv.u) (iv.u - (ring + 1)))
                (usedMask.lor (Nat.shiftLeft 1 (getImgNat img iv.u))) =
                some (invFinal, usedFinal) := by
            by_cases hble2 : (getImgNat img iv.u).ble (2 * deg) = true
            · simp only [hble2, ↓reduceIte] at hinit
              exact ⟨fun hgt => absurd (Nat.le_of_ble_eq_true hble2) (by omega), hinit⟩
            · have hble2f : (getImgNat img iv.u).ble (2 * deg) = false :=
                Bool.eq_false_iff.mpr hble2
              simp only [hble2f, Bool.false_eq_true, ↓reduceIte] at hinit
              split at hinit
              · rename_i hokFan
                simp only [Bool.and_eq_true] at hokFan
                refine ⟨fun _ => ⟨?_, Nat.le_of_ble_eq_true hokFan.2⟩, hinit⟩
                intro hz
                change getExactDegStrict deg st ((getImgNat img iv.u - 1).mod deg + 1) = 0 at hz
                rw [hz] at hokFan
                simp at hokFan
              · simp at hinit
          have hrest_bnd : ∀ iv' ∈ rest, ring + 1 ≤ iv'.u ∧ iv'.u ≤ ring + 12 :=
            fun iv' hmem => hbnd iv' (List.mem_cons_of_mem iv hmem)
          obtain ⟨hmono, hmask, hmem_rest, hinj_rest⟩ := ih hrest_bnd hinit_tail
          refine ⟨?_, ?_, ?_, ?_⟩
          · intro k hk
            apply hmono
            rw [testBit_lor_shiftLeft_one]
            simp [hk]
          · intro k
            rw [hmask k, testBit_lor_shiftLeft_one, Bool.or_eq_true, decide_eq_true_eq]
            constructor
            · intro hk_or
              rcases hk_or with (hk | hk) | ⟨iv', hmem', rfl⟩
              · exact Or.inr ⟨iv, List.mem_cons_self, hk.symm⟩
              · exact Or.inl hk
              · exact Or.inr ⟨iv', List.mem_cons_of_mem iv hmem', rfl⟩
            · intro hk_or
              rcases hk_or with hk | ⟨iv', hmem', hkeq⟩
              · exact Or.inl (Or.inr hk)
              · rcases List.mem_cons.mp hmem' with rfl | hmem'
                · exact Or.inl (Or.inl hkeq.symm)
                · exact Or.inr ⟨iv', hmem', hkeq⟩
          · intro iv' hiv'
            rcases List.mem_cons.mp hiv' with heq_iv | hmem'
            · rw [heq_iv]
              have hiv_u : iv.u - (ring + 1) < 12 := by
                have hb := hbnd iv List.mem_cons_self; omega
              have hslot_new : (usedMask.lor (Nat.shiftLeft 1 (getImgNat img iv.u))).testBit
                  (getImgNat img iv.u) = true := by
                rw [testBit_lor_shiftLeft_one]; simp
              have hnot_rest : ¬ ∃ iv'' ∈ rest, getImgNat img iv''.u = getImgNat img iv.u := by
                rintro ⟨iv'', hiv'', heq⟩
                have hf := (hmem_rest iv'' hiv'').2.1
                rw [heq, hslot_new] at hf
                contradiction
              have hinv_preserve : ∀ ivs',
                  (∀ x, x ∈ ivs' → getImgNat img x.u ≠ getImgNat img iv.u) →
                  ∀ u' m' ifin ufin,
                    initIsoVertsAux deg ring st img ivs' u' m' = some (ifin, ufin) →
                    getLaneNat ifin (getImgNat img iv.u) = getLaneNat u' (getImgNat img iv.u) := by
                intro ivs' hne_ivs' u' m' ifin ufin haux
                induction ivs' generalizing u' m' with
                | nil =>
                  simp only [initIsoVertsAux, Option.some.injEq, Prod.mk.injEq] at haux
                  rcases haux with ⟨rfl, _⟩; rfl
                | cons hd tl ihtl =>
                  dsimp only [initIsoVertsAux] at haux
                  split at haux
                  · rename_i hble_hd
                    have hne_hd := hne_ivs' hd List.mem_cons_self
                    have hle_hd : getImgNat img hd.u ≤ 5 * deg := Nat.le_of_ble_eq_true hble_hd
                    have hlt_hd : getImgNat img hd.u < 60 := by omega
                    split at haux
                    · simp at haux
                    · split at haux
                      · by_cases hble2_hd : (getImgNat img hd.u).ble (2 * deg) = true
                        · simp only [hble2_hd, ↓reduceIte] at haux
                          rw [ihtl (fun x hx => hne_ivs' x (List.mem_cons_of_mem hd hx)) _ _ haux]
                          exact getLaneNat_setLaneNat_ne _ _ _ _ hlt_hd hfu_lt60 hne_hd.symm
                        · have hble2f_hd : (getImgNat img hd.u).ble (2 * deg) = false :=
                            Bool.eq_false_iff.mpr hble2_hd
                          simp only [hble2f_hd, Bool.false_eq_true, ↓reduceIte] at haux
                          split at haux
                          · rw [ihtl (fun x hx => hne_ivs' x (List.mem_cons_of_mem hd hx)) _ _ haux]
                            exact getLaneNat_setLaneNat_ne _ _ _ _ hlt_hd hfu_lt60 hne_hd.symm
                          · simp at haux
                      · simp at haux
                  · simp at haux
              have hpres := hinv_preserve rest (fun iv'' hiv'' heq => hnot_rest ⟨iv'', hiv'', heq⟩)
                _ _ invFinal usedFinal hinit_tail
              have hval63 : (iv.u - (ring + 1)).land 63 = iv.u - (ring + 1) := by
                change (iv.u - (ring + 1)) &&& 63 = iv.u - (ring + 1)
                rw [sixThree_eq, Nat.and_two_pow_sub_one_eq_mod]
                exact Nat.mod_eq_of_lt (by omega)
              refine ⟨hfu_le, hbit_false, hivd, hfan_prop, ?_⟩
              rw [hpres, getLaneNat_setLaneNat_eq _ _ _ hfu_lt60, hval63]
            · have h_nbit : (usedMask.lor (Nat.shiftLeft 1 (getImgNat img iv.u))).testBit
                  (getImgNat img iv'.u) = false := (hmem_rest iv' hmem').2.1
              have hiv'_false : usedMask.testBit (getImgNat img iv'.u) = false := by
                cases hm : usedMask.testBit (getImgNat img iv'.u)
                · rfl
                · rw [testBit_lor_shiftLeft_one, hm, Bool.or_true] at h_nbit
                  contradiction
              exact ⟨(hmem_rest iv' hmem').1, hiv'_false, (hmem_rest iv' hmem').2.2⟩
          · intro i j hi hj hne
            cases i with
            | zero =>
              cases j with
              | zero => exact absurd rfl hne
              | succ j' =>
                intro heq
                simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
                have hj_mem : rest[j']'(Nat.lt_of_succ_lt_succ hj) ∈ rest :=
                  List.getElem_mem _
                have hfalse := (hmem_rest _ hj_mem).2.1
                rw [← heq, testBit_lor_shiftLeft_one] at hfalse
                simp at hfalse
            | succ i' =>
              cases j with
              | zero =>
                intro heq
                simp only [List.getElem_cons_zero, List.getElem_cons_succ] at heq
                have hi_mem : rest[i']'(Nat.lt_of_succ_lt_succ hi) ∈ rest :=
                  List.getElem_mem _
                have hfalse := (hmem_rest _ hi_mem).2.1
                rw [heq, testBit_lor_shiftLeft_one] at hfalse
                simp at hfalse
              | succ j' =>
                simp only [List.getElem_cons_succ]
                exact hinj_rest i' j' (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj)
                  (by omega)
        · simp at hinit
    · simp at hinit

private def checkSpokeMaskAux (deg usedMask k : Nat) : Bool :=
  match k with
  | 0 => true
  | j + 1 =>
    if checkSpokeMaskAux deg usedMask j = true then
      let w1 := j + 1
      let w2 := deg + w1
      let w3 := if w1.beq 1 then 2 * deg else (deg + w1) - 1
      if (((usedMask.shiftRight w1).land 1).beq 0 &&
         !((usedMask.shiftRight w2).land 1).beq 0 &&
         !((usedMask.shiftRight w3).land 1).beq 0) = true then false else true
    else false

private theorem checkSpokeMaskRec_eq_aux (deg usedMask : Nat) :
    checkSpokeMaskRec deg usedMask = checkSpokeMaskAux deg usedMask deg := by
  suffices h : ∀ k,
      Nat.rec true
        (fun j ih =>
          Bool.rec false
            (strictNat (j.add 1) fun w1 =>
              have w2 := deg.add w1;
              have w3 := Bool.rec ((deg.add w1).sub 1) (Nat.mul 2 deg) (w1.beq 1);
              Bool.rec true false
                (((usedMask.shiftRight w1).land 1).beq 0 && !((usedMask.shiftRight w2).land 1).beq 0 &&
                  !((usedMask.shiftRight w3).land 1).beq 0))
            ih)
        k = checkSpokeMaskAux deg usedMask k from h deg
  intro k
  induction k with
  | zero => rfl
  | succ j ih =>
    dsimp only [checkSpokeMaskAux]
    rw [← ih]
    simp only [strictNat_eq, bool_rec_eq, Nat.add_eq, Nat.sub_eq, Nat.mul_eq]

private theorem checkSpokeMaskRec_sound {deg usedMask : Nat}
    (hchk : checkSpokeMaskRec deg usedMask = true) :
    ∀ j, j < deg →
      let w1 := j + 1
      let w2 := deg + w1
      let w3 := if w1 = 1 then 2 * deg else deg + w1 - 1
      usedMask.testBit w1 = false →
        ¬ (usedMask.testBit w2 = true ∧ usedMask.testBit w3 = true) := by
  have haux : ∀ k, checkSpokeMaskAux deg usedMask k = true →
      ∀ j, j < k →
        usedMask.testBit (j + 1) = false →
          ¬ (usedMask.testBit (deg + (j + 1)) = true ∧
            usedMask.testBit (if j + 1 = 1 then 2 * deg else deg + (j + 1) - 1) = true) := by
    intro k
    induction k with
    | zero => intro _ _ _; omega
    | succ k' ih =>
      intro hk j hj hw1
      rintro ⟨hw2, hw3⟩
      dsimp only [checkSpokeMaskAux] at hk
      split at hk
      · rename_i hk'
        by_cases hjk : j < k'
        · exact ih hk' j hjk hw1 ⟨hw2, hw3⟩
        · have hj_eq : j = k' := by omega
          subst hj_eq
          by_cases hcond :
              (((usedMask.shiftRight (j + 1)).land 1).beq 0 &&
                !((usedMask.shiftRight (deg + (j + 1))).land 1).beq 0 &&
                !((usedMask.shiftRight (if (j + 1).beq 1 = true then 2 * deg else deg + (j + 1) - 1)).land 1).beq 0) = true
          · simp only [hcond, ↓reduceIte] at hk; contradiction
          · apply hcond
            simp only [Bool.and_eq_true, Bool.not_eq_true', mask_beq_zero_eq_not_testBit,
              Bool.not_eq_false', hw1, Bool.not_false, hw2, true_and]
            by_cases hj1 : j + 1 = 1
            · have hb : (j + 1).beq 1 = true := by rw [hj1]; rfl
              simp only [hb, ↓reduceIte]
              simpa [hj1] using hw3
            · have hb : (j + 1).beq 1 = false := by
                cases h : (j + 1).beq 1
                · rfl
                · exact absurd (Nat.eq_of_beq_eq_true h) hj1
              have hj0 : j ≠ 0 := by omega
              simp only [hb, Bool.false_eq_true, ↓reduceIte]
              simpa [hj0] using hw3
      · contradiction
  rw [checkSpokeMaskRec_eq_aux] at hchk
  exact haux deg hchk

private noncomputable def checkAllInduAux (deg st usedMask invMap adjMat k : Nat) : Bool :=
  match k with
  | 0 => true
  | j + 1 =>
    if checkAllInduAux deg st usedMask invMap adjMat j = true then
      let i := j + 1
      let h := if i.beq 1 then deg else i - 1
      let a := h + deg
      if (checkInduStrict usedMask invMap adjMat 0 i &&
         checkInduStrict usedMask invMap adjMat h i &&
         checkInduStrict usedMask invMap adjMat h a &&
         checkInduStrict usedMask invMap adjMat i a) = true then
        let ex := getExactDegStrict deg st i
        if ex.beq 0 then true
        else
          let b := deg + i
          if ex.beq 5 then checkInduStrict usedMask invMap adjMat a b
          else
            let c := 2 * deg + i
            if (checkInduStrict usedMask invMap adjMat a c &&
               checkInduStrict usedMask invMap adjMat c i) = true then
              if ex.beq 6 then checkInduStrict usedMask invMap adjMat c b
              else
                let d := 3 * deg + i
                if (checkInduStrict usedMask invMap adjMat c d &&
                   checkInduStrict usedMask invMap adjMat d i) = true then
                  if ex.beq 7 then checkInduStrict usedMask invMap adjMat d b
                  else if ex.beq 8 then
                    let e := 4 * deg + i
                    checkInduStrict usedMask invMap adjMat e d &&
                    checkInduStrict usedMask invMap adjMat e i &&
                    checkInduStrict usedMask invMap adjMat e b
                  else false
                else false
            else false
      else false
    else false

private theorem checkAllInduRec_eq_aux (deg st usedMask invMap adjMat : Nat) :
    checkAllInduRec deg st usedMask invMap adjMat =
      checkAllInduAux deg st usedMask invMap adjMat deg := by
  suffices h : ∀ k,
      Nat.rec true
        (fun j ih =>
          Bool.rec false
            (strictNat (j.add 1) fun i =>
              strictNat (Bool.rec (i.sub 1) deg (i.beq 1)) fun h =>
                strictNat (h.add deg) fun a =>
                  Bool.rec false
                    (strictNat (getExactDegStrict deg st i) fun ex =>
                      Bool.rec
                        (strictNat (deg.add i) fun b =>
                          Bool.rec
                            (strictNat ((Nat.mul 2 deg).add i) fun c =>
                              Bool.rec false
                                (Bool.rec
                                  (strictNat ((Nat.mul 3 deg).add i) fun d =>
                                    Bool.rec false
                                      (Bool.rec
                                        (Bool.rec false
                                          (strictNat ((Nat.mul 4 deg).add i) fun e =>
                                            checkInduStrict usedMask invMap adjMat e d &&
                                                checkInduStrict usedMask invMap adjMat e i &&
                                              checkInduStrict usedMask invMap adjMat e b)
                                          (ex.beq 8))
                                        (checkInduStrict usedMask invMap adjMat d b) (ex.beq 7))
                                      (checkInduStrict usedMask invMap adjMat c d &&
                                        checkInduStrict usedMask invMap adjMat d i))
                                  (checkInduStrict usedMask invMap adjMat c b) (ex.beq 6))
                                (checkInduStrict usedMask invMap adjMat a c &&
                                  checkInduStrict usedMask invMap adjMat c i))
                            (checkInduStrict usedMask invMap adjMat a b) (ex.beq 5))
                        true (ex.beq 0))
                    (checkInduStrict usedMask invMap adjMat 0 i &&
                        checkInduStrict usedMask invMap adjMat h i &&
                        checkInduStrict usedMask invMap adjMat h a &&
                      checkInduStrict usedMask invMap adjMat i a))
            ih)
        k = checkAllInduAux deg st usedMask invMap adjMat k from h deg
  intro k
  induction k with
  | zero => rfl
  | succ j ih =>
    dsimp only [checkAllInduAux]
    rw [← ih]
    simp only [strictNat_eq, bool_rec_eq, Nat.add_eq, Nat.sub_eq, Nat.mul_eq]

private theorem checkInduStrict_sound {usedMask invMap adjMat p q : Nat}
    (hc : checkInduStrict usedMask invMap adjMat p q = true)
    (hp : usedMask.testBit p = true) (hq : usedMask.testBit q = true) :
    adjMat.testBit ((getLaneNat invMap p) * 12 + (getLaneNat invMap q)) = true := by
  unfold checkInduStrict at hc
  have hzero : ((((usedMask.shiftRight p).land (usedMask.shiftRight q)).land 1).beq 0) = false := by
    have hbit : (((usedMask.shiftRight p).land (usedMask.shiftRight q)).land 1) = 1 := by
      apply Nat.eq_of_testBit_eq
      intro b
      by_cases hb : b = 0
      · subst hb
        rw [testBit_land_eq, testBit_land_eq, testBit_shiftRight_eq, testBit_shiftRight_eq]
        simp [hp, hq]
      · have hb1 : 1 ≤ b := Nat.one_le_iff_ne_zero.mpr hb
        have hpow : 2 ≤ 2 ^ b := by
          calc (2 : Nat) = 2 ^ 1 := by decide
            _ ≤ 2 ^ b := Nat.pow_le_pow_right (by decide) hb1
        have hl : ((usedMask.shiftRight p).land (usedMask.shiftRight q)).land 1 < 2 := by
          change ((usedMask >>> p) &&& (usedMask >>> q)) &&& 1 < 2 ^ 1
          exact Nat.and_lt_two_pow _ (by decide)
        rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hl hpow),
          Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (by decide) hpow)]
    rw [hbit]; rfl
  simp only [hzero] at hc
  have h1 : (((adjMat.shiftRight ((getLaneNat invMap p * 12) + getLaneNat invMap q)).land 1).beq 0) = false := by
    cases hz : ((adjMat.shiftRight ((getLaneNat invMap p).mul 12 |>.add (getLaneNat invMap q))).land 1).beq 0
    · rfl
    · rw [hz] at hc; contradiction
  rw [mask_beq_zero_eq_not_testBit] at h1
  simpa using h1

private theorem adjMat_c_adj_iff {h : Nat} (hh : h < 633) {fc : FastConf}
    (hfc : fc = lookupFastConfRec h) {invMap usedMask : Nat}
    {img : Nat}
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (hinit_ok : ∀ p, usedMask.testBit p = true →
      getLaneNat invMap p < (configOfRConf (parsedRConfList[h]'hlen)).interiorSize ∧
      ∃ iv ∈ fc.intVerts, getImgNat img iv.u = p ∧
        iv.u = (configOfRConf (parsedRConfList[h]'hlen)).ringSize + getLaneNat invMap p + 1)
    {p q : Nat} (hp : usedMask.testBit p = true) (hq : usedMask.testBit q = true)
    (hbit : fc.adjMat.testBit ((getLaneNat invMap p) * 12 + (getLaneNat invMap q)) = true) :
    let c := configOfRConf (parsedRConfList[h]'hlen)
    let u0 := c.ringSize + getLaneNat invMap p
    let v0 := c.ringSize + getLaneNat invMap q
    c.adj u0 v0 = true ∧ c.adj v0 u0 = true := by
  intro c u0 v0
  have hadj := (fastConf_equiv_adj h hh).2.2.2
    (getLaneNat invMap p) (hinit_ok p hp).1
    (getLaneNat invMap q) (hinit_ok q hq).1
  rw [← hfc] at hadj
  have hdir : c.adj u0 v0 = true := by rw [← hadj]; exact hbit
  have hu0 : u0 < c.totalNodes := by
    dsimp only [c, u0, Configuration.totalNodes]; exact Nat.add_lt_add_left (hinit_ok p hp).1 _
  have hv0 : v0 < c.totalNodes := by
    dsimp only [c, v0, Configuration.totalNodes]; exact Nat.add_lt_add_left (hinit_ok q hq).1 _
  have hsym := (fastConf_equiv_adj h hh).2.2.1 u0 hu0 v0 hv0
  exact ⟨hdir, by rw [← hsym.1]; exact hdir⟩

private theorem nat_beq_eq (a b : Nat) : a.beq b = (a == b) := by
  by_cases h : a = b
  · subst h
    have h1 : a.beq a = true := by
      induction a with
      | zero => rfl
      | succ _ ih => exact ih
    have h2 : (a == a) = true := beq_self_eq_true a
    rw [h1, h2]
  · have h1 : a.beq b = false := Bool.eq_false_iff.mpr fun he => h (Nat.eq_of_beq_eq_true he)
    have h2 : (a == b) = false := Bool.eq_false_iff.mpr fun he => h (eq_of_beq he)
    rw [h1, h2]

private theorem fanTri63Strict_eq_pureTriAdj (x y z u v : Nat) :
    fanTri63Strict x y z u v = pureTriAdj x y z u v := by
  dsimp only [fanTri63Strict, pureTriAdj]
  simp only [bool_rec_eq, nat_beq_eq]

private theorem pureTriAdj_elems {x y z u v w : Nat} (hw : w ≠ 63)
    (h : pureTriAdj x y z u v = w) :
    (u = x ∧ v = y ∧ w = z) ∨ (u = y ∧ v = z ∧ w = x) ∨ (u = z ∧ v = x ∧ w = y) := by
  dsimp only [pureTriAdj] at h
  by_cases h1 : (u == x && v == y) = true
  · simp only [h1, ↓reduceIte] at h
    simp only [Bool.and_eq_true, beq_iff_eq] at h1
    exact Or.inl ⟨h1.1, h1.2, h.symm⟩
  · by_cases h2 : (u == y && v == z) = true
    · simp only [h1, Bool.false_eq_true, ↓reduceIte, h2] at h
      simp only [Bool.and_eq_true, beq_iff_eq] at h2
      exact Or.inr (Or.inl ⟨h2.1, h2.2, h.symm⟩)
    · by_cases h3 : (u == z && v == x) = true
      · simp only [h1, h2, Bool.false_eq_true, ↓reduceIte, h3] at h
        simp only [Bool.and_eq_true, beq_iff_eq] at h3
        exact Or.inr (Or.inr ⟨h3.1, h3.2, h.symm⟩)
      · simp only [h1, h2, h3, Bool.false_eq_true, ↓reduceIte] at h
        exact absurd h.symm hw

private theorem pureTriAdj_rot_left {x y z u v w : Nat} (h : pureTriAdj x y z u v = w)
    (hw : w ≠ 63) (hx63 : x ≠ 63) (hy63 : y ≠ 63) (hz63 : z ≠ 63)
    (hxy : x ≠ y) (hyz : y ≠ z) (hxz : x ≠ z) :
    pureTriAdj x y z v w = u ∧ pureTriAdj x y z w u = v := by
  rcases pureTriAdj_elems hw h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ <;>
    constructor <;>
    · dsimp only [pureTriAdj]
      simp only [Bool.and_eq_true, beq_iff_eq]
      split
      · omega
      · split
        · first | rfl | omega
        · split
          · first | rfl | omega
          · simp_all

private theorem mod_mul_add_sub_one (m deg i : Nat) (hi1 : 1 ≤ i) (hi_deg : i ≤ deg) :
    (m * deg + i - 1) % deg + 1 = i := by
  have h1 : m * deg + i - 1 = (i - 1) + deg * m := by
    rw [Nat.add_sub_assoc hi1, Nat.mul_comm m deg, Nat.add_comm]
  rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  omega

private theorem initIsoVertsRec_sound {h : Nat} (hh : h < 633)
    {deg cur img invMap usedMask : Nat} (hdeg11 : deg ≤ 11)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (hinit : initIsoVertsRec deg (lookupFastConfRec h).ring cur img
      (lookupFastConfRec h).intVerts = some (invMap, usedMask)) :
    let fc := lookupFastConfRec h
    let c := configOfRConf (parsedRConfList[h]'hlen)
    (∀ k, usedMask.testBit k = true ↔ ∃ iv ∈ fc.intVerts, getImgNat img iv.u = k) ∧
    (∀ p, usedMask.testBit p = true →
      getLaneNat invMap p < c.interiorSize ∧
      ∃ iv ∈ fc.intVerts, getImgNat img iv.u = p ∧
        iv.u = c.ringSize + getLaneNat invMap p + 1) ∧
    (∀ iv ∈ fc.intVerts,
      getImgNat img iv.u ≤ 5 * deg ∧
      iv.d = getUppStrict deg cur (getImgNat img iv.u) ∧
      (getImgNat img iv.u > 2 * deg →
        let fu := getImgNat img iv.u
        let i := (fu - 1) % deg + 1
        getExactDegStrict deg cur i ≠ 0 ∧ (fu - 1) / deg + 4 ≤ getExactDegStrict deg cur i) ∧
      getLaneNat invMap (getImgNat img iv.u) = iv.u - (c.ringSize + 1)) ∧
    (∀ iv1 ∈ fc.intVerts, ∀ iv2 ∈ fc.intVerts,
      iv1.u ≠ iv2.u → getImgNat img iv1.u ≠ getImgNat img iv2.u) := by
  intro fc c
  have hhdr := fastConf_equiv_header h hh
  have hivs := fastConf_equiv_intVerts h hh
  have hring : fc.ring = c.ringSize := hhdr.1
  have hlen_ivs : fc.intVerts.length = c.interiorSize := hhdr.2.2.2.2.2.2.2.2.2.2.1
  have hint12 : c.interiorSize ≤ 12 := hhdr.2.2.2.2.2.2.2.2.1
  have hbnd : ∀ iv ∈ fc.intVerts, fc.ring + 1 ≤ iv.u ∧ iv.u ≤ fc.ring + 12 := by
    intro iv hiv
    rcases List.mem_iff_getElem.mp hiv with ⟨iu, hiu, rfl⟩
    have hiu_c : iu < c.interiorSize := by rw [← hlen_ivs]; exact hiu
    have hu := (hivs iu hiu_c).1
    dsimp only [fc, c] at hring hu ⊢
    omega
  rw [initIsoVertsRec_eq_aux] at hinit
  obtain ⟨_, hmask_iff, hmem_spec, hinj⟩ := initIsoVertsAux_spec hdeg11 hbnd hinit
  have hmask' : ∀ k, usedMask.testBit k = true ↔ ∃ iv ∈ fc.intVerts, getImgNat img iv.u = k := by
    intro k
    rw [hmask_iff k]
    constructor
    · rintro (h0 | hEx)
      · rw [Nat.zero_testBit] at h0; cases h0
      · exact hEx
    · exact Or.inr
  refine ⟨hmask', ?_, ?_, ?_⟩
  · intro p hp
    rcases (hmask' p).mp hp with ⟨iv, hiv, hpu⟩
    rcases List.mem_iff_getElem.mp hiv with ⟨iu, hiu, rfl⟩
    have hiu_c : iu < c.interiorSize := by rw [← hlen_ivs]; exact hiu
    have hu_eq := (hivs iu hiu_c).1
    have hlane := (hmem_spec _ hiv).2.2.2.2
    rw [hpu, hring, hu_eq] at hlane
    dsimp only [c] at hlane
    have hlane_iu : getLaneNat invMap p = iu := by omega
    refine ⟨?_, _, hiv, hpu, ?_⟩
    · rw [hlane_iu]; exact hiu_c
    · rw [hlane_iu]; exact hu_eq
  · intro iv hiv
    have hs := hmem_spec iv hiv
    refine ⟨hs.1, hs.2.2.1, hs.2.2.2.1, ?_⟩
    rw [← hring]; exact hs.2.2.2.2
  · intro iv1 hiv1 iv2 hiv2 hne
    rcases List.mem_iff_getElem.mp hiv1 with ⟨i, hi, rfl⟩
    rcases List.mem_iff_getElem.mp hiv2 with ⟨j, hj, rfl⟩
    have hij : i ≠ j := by
      intro heq; subst heq; exact hne rfl
    exact hinj i j hi hj hij

private theorem checkAllInduRec_spec {deg st usedMask invMap adjMat : Nat}
    (hc : checkAllInduRec deg st usedMask invMap adjMat = true) :
    ∀ i, 1 ≤ i → i ≤ deg →
      let h := if i = 1 then deg else i - 1
      let a := h + deg
      let b := deg + i
      let c := 2 * deg + i
      let d := 3 * deg + i
      let e := 4 * deg + i
      let ex := getExactDegStrict deg st i
      checkInduStrict usedMask invMap adjMat 0 i = true ∧
      checkInduStrict usedMask invMap adjMat h i = true ∧
      checkInduStrict usedMask invMap adjMat h a = true ∧
      checkInduStrict usedMask invMap adjMat i a = true ∧
      (ex ≠ 0 →
        (ex = 5 ∧ checkInduStrict usedMask invMap adjMat a b = true) ∨
        (ex = 6 ∧ checkInduStrict usedMask invMap adjMat a c = true ∧
          checkInduStrict usedMask invMap adjMat c i = true ∧
          checkInduStrict usedMask invMap adjMat c b = true) ∨
        (ex = 7 ∧ checkInduStrict usedMask invMap adjMat a c = true ∧
          checkInduStrict usedMask invMap adjMat c i = true ∧
          checkInduStrict usedMask invMap adjMat c d = true ∧
          checkInduStrict usedMask invMap adjMat d i = true ∧
          checkInduStrict usedMask invMap adjMat d b = true) ∨
        (ex = 8 ∧ checkInduStrict usedMask invMap adjMat a c = true ∧
          checkInduStrict usedMask invMap adjMat c i = true ∧
          checkInduStrict usedMask invMap adjMat c d = true ∧
          checkInduStrict usedMask invMap adjMat d i = true ∧
          checkInduStrict usedMask invMap adjMat e d = true ∧
          checkInduStrict usedMask invMap adjMat e i = true ∧
          checkInduStrict usedMask invMap adjMat e b = true)) := by
  rw [checkAllInduRec_eq_aux] at hc
  suffices haux : ∀ k, checkAllInduAux deg st usedMask invMap adjMat k = true →
      ∀ i, 1 ≤ i → i ≤ k →
        let h := if i = 1 then deg else i - 1
        let a := h + deg
        let b := deg + i
        let c := 2 * deg + i
        let d := 3 * deg + i
        let e := 4 * deg + i
        let ex := getExactDegStrict deg st i
        checkInduStrict usedMask invMap adjMat 0 i = true ∧
        checkInduStrict usedMask invMap adjMat h i = true ∧
        checkInduStrict usedMask invMap adjMat h a = true ∧
        checkInduStrict usedMask invMap adjMat i a = true ∧
        (ex ≠ 0 →
          (ex = 5 ∧ checkInduStrict usedMask invMap adjMat a b = true) ∨
          (ex = 6 ∧ checkInduStrict usedMask invMap adjMat a c = true ∧
            checkInduStrict usedMask invMap adjMat c i = true ∧
            checkInduStrict usedMask invMap adjMat c b = true) ∨
          (ex = 7 ∧ checkInduStrict usedMask invMap adjMat a c = true ∧
            checkInduStrict usedMask invMap adjMat c i = true ∧
            checkInduStrict usedMask invMap adjMat c d = true ∧
            checkInduStrict usedMask invMap adjMat d i = true ∧
            checkInduStrict usedMask invMap adjMat d b = true) ∨
          (ex = 8 ∧ checkInduStrict usedMask invMap adjMat a c = true ∧
            checkInduStrict usedMask invMap adjMat c i = true ∧
            checkInduStrict usedMask invMap adjMat c d = true ∧
            checkInduStrict usedMask invMap adjMat d i = true ∧
            checkInduStrict usedMask invMap adjMat e d = true ∧
            checkInduStrict usedMask invMap adjMat e i = true ∧
            checkInduStrict usedMask invMap adjMat e b = true)) from haux deg hc
  intro k
  induction k with
  | zero => intro _ i hi1 hi0; omega
  | succ j ih =>
    intro hchk i hi1 hij
    dsimp only [checkAllInduAux] at hchk
    by_cases hp : checkAllInduAux deg st usedMask invMap adjMat j = true
    · simp only [hp, ↓reduceIte] at hchk
      by_cases hij_le : i ≤ j
      · exact ih hp i hi1 hij_le
      · have hi_eq : i = j + 1 := by omega
        subst hi_eq
        have hbeqi : ((j + 1).beq 1) = decide (j + 1 = 1) := nat_beq_eq (j + 1) 1
        have hh_eq : (if (j + 1).beq 1 = true then deg else j + 1 - 1) =
            if j + 1 = 1 then deg else j + 1 - 1 := by
          rw [hbeqi]; simp only [decide_eq_true_eq]
        rw [hh_eq] at hchk
        by_cases hbase :
            (checkInduStrict usedMask invMap adjMat 0 (j + 1) &&
             checkInduStrict usedMask invMap adjMat (if j + 1 = 1 then deg else j + 1 - 1) (j + 1) &&
             checkInduStrict usedMask invMap adjMat (if j + 1 = 1 then deg else j + 1 - 1)
               ((if j + 1 = 1 then deg else j + 1 - 1) + deg) &&
             checkInduStrict usedMask invMap adjMat (j + 1)
               ((if j + 1 = 1 then deg else j + 1 - 1) + deg)) = true
        · simp only [hbase, ↓reduceIte] at hchk
          have hbase' := hbase
          simp only [Bool.and_eq_true] at hbase'
          rcases hbase' with ⟨⟨⟨hb0, hb1⟩, hb2⟩, hb3⟩
          refine ⟨hb0, hb1, hb2, hb3, fun hex0 => ?_⟩
          by_cases hex0b : (getExactDegStrict deg st (j + 1)).beq 0 = true
          · exact absurd (Nat.eq_of_beq_eq_true hex0b) hex0
          · have hex0f : (getExactDegStrict deg st (j + 1)).beq 0 = false :=
              Bool.eq_false_iff.mpr hex0b
            simp only [hex0f, Bool.false_eq_true, ↓reduceIte] at hchk
            by_cases hex5 : (getExactDegStrict deg st (j + 1)).beq 5 = true
            · simp only [hex5, ↓reduceIte] at hchk
              exact Or.inl ⟨Nat.eq_of_beq_eq_true hex5, hchk⟩
            · have hex5f : (getExactDegStrict deg st (j + 1)).beq 5 = false :=
                Bool.eq_false_iff.mpr hex5
              simp only [hex5f, Bool.false_eq_true, ↓reduceIte] at hchk
              by_cases hac_ci :
                  (checkInduStrict usedMask invMap adjMat
                    ((if j + 1 = 1 then deg else j + 1 - 1) + deg) (2 * deg + (j + 1)) &&
                   checkInduStrict usedMask invMap adjMat (2 * deg + (j + 1)) (j + 1)) = true
              · simp only [hac_ci, ↓reduceIte] at hchk
                have hac_ci' := hac_ci
                simp only [Bool.and_eq_true] at hac_ci'
                by_cases hex6 : (getExactDegStrict deg st (j + 1)).beq 6 = true
                · simp only [hex6, ↓reduceIte] at hchk
                  exact Or.inr (Or.inl ⟨Nat.eq_of_beq_eq_true hex6, hac_ci'.1, hac_ci'.2, hchk⟩)
                · have hex6f : (getExactDegStrict deg st (j + 1)).beq 6 = false :=
                    Bool.eq_false_iff.mpr hex6
                  simp only [hex6f, Bool.false_eq_true, ↓reduceIte] at hchk
                  by_cases hcd_di :
                      (checkInduStrict usedMask invMap adjMat (2 * deg + (j + 1)) (3 * deg + (j + 1)) &&
                       checkInduStrict usedMask invMap adjMat (3 * deg + (j + 1)) (j + 1)) = true
                  · simp only [hcd_di, ↓reduceIte] at hchk
                    have hcd_di' := hcd_di
                    simp only [Bool.and_eq_true] at hcd_di'
                    by_cases hex7 : (getExactDegStrict deg st (j + 1)).beq 7 = true
                    · simp only [hex7, ↓reduceIte] at hchk
                      exact Or.inr (Or.inr (Or.inl ⟨Nat.eq_of_beq_eq_true hex7,
                        hac_ci'.1, hac_ci'.2, hcd_di'.1, hcd_di'.2, hchk⟩))
                    · have hex7f : (getExactDegStrict deg st (j + 1)).beq 7 = false :=
                        Bool.eq_false_iff.mpr hex7
                      simp only [hex7f, Bool.false_eq_true, ↓reduceIte] at hchk
                      by_cases hex8 : (getExactDegStrict deg st (j + 1)).beq 8 = true
                      · simp only [hex8, ↓reduceIte, Bool.and_eq_true] at hchk
                        exact Or.inr (Or.inr (Or.inr ⟨Nat.eq_of_beq_eq_true hex8,
                          hac_ci'.1, hac_ci'.2, hcd_di'.1, hcd_di'.2, hchk.1.1, hchk.1.2, hchk.2⟩))
                      · have hex8f : (getExactDegStrict deg st (j + 1)).beq 8 = false :=
                          Bool.eq_false_iff.mpr hex8
                        simp only [hex8f, Bool.false_eq_true, ↓reduceIte] at hchk
                  · have hcd_dif :
                        (checkInduStrict usedMask invMap adjMat (2 * deg + (j + 1)) (3 * deg + (j + 1)) &&
                         checkInduStrict usedMask invMap adjMat (3 * deg + (j + 1)) (j + 1)) = false :=
                      Bool.eq_false_iff.mpr hcd_di
                    simp only [hcd_dif, Bool.false_eq_true, ↓reduceIte] at hchk
              · have hac_cif :
                    (checkInduStrict usedMask invMap adjMat
                      ((if j + 1 = 1 then deg else j + 1 - 1) + deg) (2 * deg + (j + 1)) &&
                     checkInduStrict usedMask invMap adjMat (2 * deg + (j + 1)) (j + 1)) = false :=
                  Bool.eq_false_iff.mpr hac_ci
                simp only [hac_cif, Bool.false_eq_true, ↓reduceIte] at hchk
        · have hbasef :
              (checkInduStrict usedMask invMap adjMat 0 (j + 1) &&
               checkInduStrict usedMask invMap adjMat (if j + 1 = 1 then deg else j + 1 - 1) (j + 1) &&
               checkInduStrict usedMask invMap adjMat (if j + 1 = 1 then deg else j + 1 - 1)
                 ((if j + 1 = 1 then deg else j + 1 - 1) + deg) &&
               checkInduStrict usedMask invMap adjMat (j + 1)
                 ((if j + 1 = 1 then deg else j + 1 - 1) + deg)) = false :=
            Bool.eq_false_iff.mpr hbase
          simp only [hbasef, Bool.false_eq_true, ↓reduceIte] at hchk
    · have hpf : checkAllInduAux deg st usedMask invMap adjMat j = false :=
        Bool.eq_false_iff.mpr hp
      simp only [hpf, Bool.false_eq_true, ↓reduceIte] at hchk

private theorem pureSpokeAdj_edge_cases {deg k i p q : Nat}
    (hk : 5 ≤ k) (h_ne : pureSpokeAdj deg i k p q ≠ 63) :
    let h := if i = 1 then deg else i - 1
    let a := deg + h
    let b := deg + i
    let c := 2 * deg + i
    let d := 3 * deg + i
    let e := 4 * deg + i
    let has := fun x y => (p = x ∧ q = y) ∨ (p = y ∧ q = x)
    has 0 i ∨ has 0 h ∨ has h i ∨ has h a ∨ has i a ∨
    (k = 5 ∧ (has a b ∨ has i b)) ∨
    (k = 6 ∧ (has a c ∨ has c i ∨ has c b ∨ has i b)) ∨
    (k = 7 ∧ (has a c ∨ has c i ∨ has c d ∨ has d i ∨ has d b ∨ has i b)) ∨
    (k = 8 ∧ (has a c ∨ has c i ∨ has c d ∨ has d i ∨ has e d ∨ has e i ∨ has e b ∨ has i b)) := by
  dsimp only [pureSpokeAdj] at h_ne
  have hbeqi : (i == 1) = decide (i = 1) := rfl
  simp only [hbeqi, decide_eq_true_eq] at h_ne
  by_cases hr1 : pureTriAdj 0 (if i = 1 then deg else i - 1) i p q = 63
  · simp only [hr1, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h_ne
    by_cases hr2 : pureTriAdj i (if i = 1 then deg else i - 1) (deg + if i = 1 then deg else i - 1) p q = 63
    · simp only [hr2, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h_ne
      by_cases hk5 : k = 5
      · subst hk5
        simp only [beq_self_eq_true, ↓reduceIte] at h_ne
        rcases pureTriAdj_elems h_ne rfl with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr ⟨rfl, rfl⟩)⟩)))))
      · have hbk5 : (k == 5) = false := Bool.eq_false_iff.mpr (by simp [hk5])
        simp only [hbk5, Bool.false_eq_true, ↓reduceIte] at h_ne
        by_cases hk6 : k = 6
        · subst hk6
          simp only [beq_self_eq_true, ↓reduceIte] at h_ne
          by_cases hr3 : pureTriAdj i (deg + if i = 1 then deg else i - 1) (2 * deg + i) p q = 63
          · simp only [hr3, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h_ne
            rcases pureTriAdj_elems h_ne rfl with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl (Or.inr ⟨rfl, rfl⟩))⟩))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩)))⟩))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))⟩))))))
          · rcases pureTriAdj_elems hr3 rfl with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩)))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩))))))
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩))⟩))))))
        · have hbk6 : (k == 6) = false := Bool.eq_false_iff.mpr (by simp [hk6])
          simp only [hbk6, Bool.false_eq_true, ↓reduceIte] at h_ne
          by_cases hk7 : k = 7
          · subst hk7
            simp only [beq_self_eq_true, ↓reduceIte] at h_ne
            by_cases hr3 : pureTriAdj i (deg + if i = 1 then deg else i - 1) (2 * deg + i) p q = 63
            · simp only [hr3, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h_ne
              by_cases hr4 : pureTriAdj i (2 * deg + i) (3 * deg + i) p q = 63
              · simp only [hr4, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h_ne
                rcases pureTriAdj_elems h_ne rfl with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨rfl, rfl⟩))))⟩)))))))
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩)))))⟩)))))))
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))⟩)))))))
              · rcases pureTriAdj_elems hr4 rfl with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl (Or.inr ⟨rfl, rfl⟩))⟩)))))))
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩)))⟩)))))))
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩))))⟩)))))))
            · rcases pureTriAdj_elems hr3 rfl with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩)))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩)))))))
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩))⟩)))))))
          · have hbk7 : (k == 7) = false := Bool.eq_false_iff.mpr (by simp [hk7])
            simp only [hbk7, Bool.false_eq_true, ↓reduceIte] at h_ne
            by_cases hk8 : k = 8
            · subst hk8
              simp only [beq_self_eq_true, ↓reduceIte] at h_ne
              by_cases hr3 : pureTriAdj i (deg + if i = 1 then deg else i - 1) (2 * deg + i) p q = 63
              · simp only [hr3, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h_ne
                by_cases hr4 : pureTriAdj i (2 * deg + i) (3 * deg + i) p q = 63
                · simp only [hr4, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h_ne
                  by_cases hr5 : pureTriAdj i (3 * deg + i) (4 * deg + i) p q = 63
                  · simp only [hr5, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h_ne
                    rcases pureTriAdj_elems h_ne rfl with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨rfl, rfl⟩))))))⟩)))))))
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩)))))))⟩)))))))
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩)))))))⟩)))))))
                  · rcases pureTriAdj_elems hr5 rfl with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨rfl, rfl⟩))))⟩)))))))
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨rfl, rfl⟩)))))⟩)))))))
                    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩))))))⟩)))))))
                · rcases pureTriAdj_elems hr4 rfl with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inl (Or.inr ⟨rfl, rfl⟩))⟩)))))))
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩)))⟩)))))))
                  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩))))⟩)))))))
              · rcases pureTriAdj_elems hr3 rfl with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩)))))
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inl (Or.inl ⟨rfl, rfl⟩)⟩)))))))
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩))⟩)))))))
            · have hbk8 : (k == 8) = false := Bool.eq_false_iff.mpr (by simp [hk8])
              simp only [hbk8, Bool.false_eq_true, ↓reduceIte] at h_ne
              exact absurd rfl h_ne
    · rcases pureTriAdj_elems hr2 rfl with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
      · exact Or.inr (Or.inr (Or.inl (Or.inr ⟨rfl, rfl⟩)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩))))
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Or.inr ⟨rfl, rfl⟩)))))
  · rcases pureTriAdj_elems hr1 rfl with ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩ | ⟨rfl, rfl, _⟩
    · exact Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩))
    · exact Or.inr (Or.inr (Or.inl (Or.inl ⟨rfl, rfl⟩)))
    · exact Or.inl (Or.inr ⟨rfl, rfl⟩)

private theorem pureCartAdj_implies_c_adj {h : Nat} (hh : h < 633)
    {deg cur img invMap usedMask : Nat} (hdeg5 : 5 ≤ deg) (hdeg11 : deg ≤ 11)
    {cartDeg : Nat → Nat} (hmin5 : ∀ r, 1 ≤ r → r ≤ 5 * deg → 5 ≤ cartDeg r)
    (hm31 : MatchesCartState31 deg cartDeg cur)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    (hinit : initIsoVertsRec deg (lookupFastConfRec h).ring cur img
      (lookupFastConfRec h).intVerts = some (invMap, usedMask))
    (hspoke : checkSpokeMaskRec deg usedMask = true)
    (hindu : checkAllInduRec deg cur usedMask invMap (lookupFastConfRec h).adjMat = true)
    (hexact : ∀ iv ∈ (lookupFastConfRec h).intVerts,
      getImgNat img iv.u ≤ 5 * deg ∧
      iv.d = getUppStrict deg cur (getImgNat img iv.u) ∧
      cartDeg (getImgNat img iv.u) = iv.d)
    {p q : Nat} (hp : usedMask.testBit p = true) (hq : usedMask.testBit q = true)
    (hpca : pureCartAdj deg cartDeg p q) :
    let c := configOfRConf (parsedRConfList[h]'hlen)
    let u0 := c.ringSize + getLaneNat invMap p
    let v0 := c.ringSize + getLaneNat invMap q
    c.adj u0 v0 = true ∧ c.adj v0 u0 = true := by
  intro c u0 v0
  have ⟨hmask_iff, hinit_ok, hmem_b, _⟩ := initIsoVertsRec_sound hh hdeg11 hlen hinit
  have hind := checkAllInduRec_spec hindu
  have hsp := checkSpokeMaskRec_sound hspoke
  have hit := fun {x y : Nat} (hx : usedMask.testBit x = true) (hy : usedMask.testBit y = true)
      (hchk : checkInduStrict usedMask invMap (lookupFastConfRec h).adjMat x y = true) =>
    adjMat_c_adj_iff hh rfl hlen hinit_ok hx hy (checkInduStrict_sound hchk hx hy)
  have hit_or : ∀ {x y : Nat},
      ((p = x ∧ q = y) ∨ (p = y ∧ q = x)) →
      checkInduStrict usedMask invMap (lookupFastConfRec h).adjMat x y = true →
      c.adj u0 v0 = true ∧ c.adj v0 u0 = true := by
    intro x y hxy hchk
    rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hit hp hq hchk
    · have := hit hq hp hchk
      exact ⟨this.2, this.1⟩
  rcases hpca with ⟨i, hi1, hi_deg, hdir⟩
  have hcd5 : 5 ≤ cartDeg i := hmin5 i hi1 (by omega)
  have hstep : ∀ {p' q' : Nat}, usedMask.testBit p' = true → usedMask.testBit q' = true →
      (c.ringSize + getLaneNat invMap p' = u0 ∧ c.ringSize + getLaneNat invMap q' = v0 ∨
       c.ringSize + getLaneNat invMap p' = v0 ∧ c.ringSize + getLaneNat invMap q' = u0) →
      pureSpokeAdj deg i (cartDeg i) p' q' ≠ 63 →
      c.adj u0 v0 = true ∧ c.adj v0 u0 = true := by
    intro p' q' hp' hq' huv hne
    have hcase := pureSpokeAdj_edge_cases hcd5 hne
    have hl : ∀ {x y : Nat}, ((p' = x ∧ q' = y) ∨ (p' = y ∧ q' = x)) →
        checkInduStrict usedMask invMap (lookupFastConfRec h).adjMat x y = true →
        c.adj u0 v0 = true ∧ c.adj v0 u0 = true := by
      intro x y hxy hchk
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hpair := hit hp' hq' hchk
        dsimp only at hpair
        rcases huv with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2] at hpair; exact hpair
        · rw [h1, h2] at hpair; exact ⟨hpair.2, hpair.1⟩
      · have hpair := hit hq' hp' hchk
        dsimp only at hpair
        rcases huv with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2] at hpair; exact ⟨hpair.2, hpair.1⟩
        · rw [h1, h2] at hpair; exact hpair
    let hs := if i = 1 then deg else i - 1
    let a := deg + hs
    let b := deg + i
    let cv := 2 * deg + i
    let d := 3 * deg + i
    let e := 4 * deg + i
    have hsi1 : 1 ≤ hs := by dsimp only [hs]; split <;> omega
    have hsi_deg : hs ≤ deg := by dsimp only [hs]; split <;> omega
    let inext := if i = deg then 1 else i + 1
    have hni1 : 1 ≤ inext := by dsimp only [inext]; split <;> omega
    have hni_deg : inext ≤ deg := by dsimp only [inext]; split <;> omega
    have hnh : (if inext = 1 then deg else inext - 1) = i := by
      dsimp only [inext]; split
      · rename_i heq; exact heq.symm
      · rename_i hne2
        split
        · omega
        · omega
    have hind_i := hind i hi1 hi_deg
    have hind_hs := hind hs hsi1 hsi_deg
    have hind_in := hind inext hni1 hni_deg
    dsimp only at hind_i hind_hs hind_in
    have ha_comm : (if i = 1 then deg else i - 1) + deg = a := Nat.add_comm _ deg
    have hsp_ex : usedMask.testBit cv = true ∨ usedMask.testBit d = true ∨
        usedMask.testBit e = true →
        getExactDegStrict deg cur i = cartDeg i := by
      intro hor
      have hex_ne : getExactDegStrict deg cur i ≠ 0 := by
        rcases hor with hc | hd_b | he_b
        · rcases (hmask_iff cv).mp hc with ⟨iv, hiv, hcv⟩
          have hf := (hmem_b iv hiv).2.2.1
          rw [hcv] at hf
          dsimp only [cv] at hf
          have hmod := mod_mul_add_sub_one 2 deg i hi1 hi_deg
          rw [hmod] at hf
          exact (hf (by omega)).1
        · rcases (hmask_iff d).mp hd_b with ⟨iv, hiv, hd⟩
          have hf := (hmem_b iv hiv).2.2.1
          rw [hd] at hf
          dsimp only [d] at hf
          have hmod := mod_mul_add_sub_one 3 deg i hi1 hi_deg
          rw [hmod] at hf
          exact (hf (by omega)).1
        · rcases (hmask_iff e).mp he_b with ⟨iv, hiv, he⟩
          have hf := (hmem_b iv hiv).2.2.1
          rw [he] at hf
          dsimp only [e] at hf
          have hmod := mod_mul_add_sub_one 4 deg i hi1 hi_deg
          rw [hmod] at hf
          exact (hf (by omega)).1
      exact (cartDeg_eq_exactDeg_of_ne_zero hm31 hi1 (by omega) hcd5 hex_ne).2.1.symm
    rcases hcase with h0i | h0h | hhi | hha | hia | ⟨hk5, hk5c⟩ | ⟨hk6, hk6c⟩ | ⟨hk7, hk7c⟩ | ⟨hk8, hk8c⟩
    · exact hl h0i hind_i.1
    · exact hl h0h hind_hs.1
    · exact hl hhi hind_i.2.1
    · rw [ha_comm] at hind_i
      exact hl hha hind_i.2.2.1
    · rw [ha_comm] at hind_i
      exact hl hia hind_i.2.2.2.1
    · rcases hk5c with hab | hib
      · have ⟨ha_b, hb_b⟩ : usedMask.testBit a = true ∧ usedMask.testBit b = true := by
          rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> (first | exact ⟨hp', hq'⟩ | exact ⟨hq', hp'⟩)
        have hi_mask : usedMask.testBit i = true := by
          apply Decidable.byContradiction
          intro hi_f
          have hi_f' : usedMask.testBit i = false := Bool.eq_false_iff.mpr hi_f
          have hforb := hsp (i - 1) (by omega)
          dsimp only at hforb
          have hw1 : (i - 1) + 1 = i := by omega
          rw [hw1] at hforb
          have hw3_eq : (if i = 1 then 2 * deg else deg + i - 1) = a := by
            dsimp only [a, hs]
            by_cases hi1' : i = 1 <;> simp [hi1'] <;> omega
          rw [hw3_eq] at hforb
          exact hforb hi_f' ⟨hb_b, ha_b⟩
        rcases (hmask_iff i).mp hi_mask with ⟨iv, hiv, hiu⟩
        have hupp5 : getUppStrict deg cur i = 5 := by
          have ⟨_, hd_upp, hcd_iv⟩ := hexact iv hiv
          rw [hiu] at hd_upp hcd_iv
          omega
        have hex5 : getExactDegStrict deg cur i = 5 :=
          getExactDeg_eq_5_of_upp_eq_5 hm31 hi1 (by omega) hcd5 hupp5
        rcases hind_i.2.2.2.2 (by omega) with ⟨_, hchk_ab⟩ | ⟨hex6, _⟩ | ⟨hex7, _⟩ | ⟨hex8, _⟩
        · rw [ha_comm] at hchk_ab
          exact hl hab hchk_ab
        · omega
        · omega
        · omega
      · have h_in := hind_in.2.2.1
        rw [hnh] at h_in
        rw [Nat.add_comm i deg] at h_in
        exact hl hib h_in
    · rcases hk6c with hac | hci | hcb | hib
      · have hcv : usedMask.testBit cv = true := by
          rcases hac with ⟨_, rfl⟩ | ⟨rfl, _⟩ <;> (first | exact hq' | exact hp')
        have hex6 : getExactDegStrict deg cur i = 6 := by rw [hsp_ex (Or.inl hcv), hk6]
        rcases hind_i.2.2.2.2 (by omega) with ⟨hex5, _⟩ | ⟨_, h_ac, _, _⟩ | ⟨hex7, _⟩ | ⟨hex8, _⟩ <;>
          try omega
        rw [ha_comm] at h_ac
        exact hl hac h_ac
      · have hcv : usedMask.testBit cv = true := by
          rcases hci with ⟨rfl, _⟩ | ⟨_, rfl⟩ <;> (first | exact hp' | exact hq')
        have hex6 : getExactDegStrict deg cur i = 6 := by rw [hsp_ex (Or.inl hcv), hk6]
        rcases hind_i.2.2.2.2 (by omega) with ⟨hex5, _⟩ | ⟨_, _, h_ci, _⟩ | ⟨hex7, _⟩ | ⟨hex8, _⟩ <;>
          try omega
        exact hl hci h_ci
      · have hcv : usedMask.testBit cv = true := by
          rcases hcb with ⟨rfl, _⟩ | ⟨_, rfl⟩ <;> (first | exact hp' | exact hq')
        have hex6 : getExactDegStrict deg cur i = 6 := by rw [hsp_ex (Or.inl hcv), hk6]
        rcases hind_i.2.2.2.2 (by omega) with ⟨hex5, _⟩ | ⟨_, _, _, h_cb⟩ | ⟨hex7, _⟩ | ⟨hex8, _⟩ <;>
          try omega
        exact hl hcb h_cb
      · have h_in := hind_in.2.2.1; rw [hnh] at h_in; rw [Nat.add_comm i deg] at h_in
        exact hl hib h_in
    · rcases hk7c with hac | hci | hcd | hdi | hdb | hib
      · have hcv : usedMask.testBit cv = true := by
          rcases hac with ⟨_, rfl⟩ | ⟨rfl, _⟩ <;> (first | exact hq' | exact hp')
        have hex7 : getExactDegStrict deg cur i = 7 := by rw [hsp_ex (Or.inl hcv), hk7]
        rcases hind_i.2.2.2.2 (by omega) with ⟨hex5, _⟩ | ⟨hex6, _⟩ | ⟨_, h_ac, _⟩ | ⟨hex8, _⟩ <;>
          try omega
        rw [ha_comm] at h_ac; exact hl hac h_ac
      · have hcv : usedMask.testBit cv = true := by
          rcases hci with ⟨rfl, _⟩ | ⟨_, rfl⟩ <;> (first | exact hp' | exact hq')
        have hex7 : getExactDegStrict deg cur i = 7 := by rw [hsp_ex (Or.inl hcv), hk7]
        rcases hind_i.2.2.2.2 (by omega) with ⟨hex5, _⟩ | ⟨hex6, _⟩ | ⟨_, _, h_ci, _⟩ | ⟨hex8, _⟩ <;>
          try omega
        exact hl hci h_ci
      · have hd_b : usedMask.testBit d = true := by
          rcases hcd with ⟨_, rfl⟩ | ⟨rfl, _⟩ <;> (first | exact hq' | exact hp')
        have hex7 : getExactDegStrict deg cur i = 7 := by rw [hsp_ex (Or.inr (Or.inl hd_b)), hk7]
        rcases hind_i.2.2.2.2 (by omega) with ⟨hex5, _⟩ | ⟨hex6, _⟩ | ⟨_, _, _, h_cd, _⟩ | ⟨hex8, _⟩ <;>
          try omega
        exact hl hcd h_cd
      · have hd_b : usedMask.testBit d = true := by
          rcases hdi with ⟨rfl, _⟩ | ⟨_, rfl⟩ <;> (first | exact hp' | exact hq')
        have hex7 : getExactDegStrict deg cur i = 7 := by rw [hsp_ex (Or.inr (Or.inl hd_b)), hk7]
        rcases hind_i.2.2.2.2 (by omega) with ⟨hex5, _⟩ | ⟨hex6, _⟩ | ⟨_, _, _, _, h_di, _⟩ | ⟨hex8, _⟩ <;>
          try omega
        exact hl hdi h_di
      · have hd_b : usedMask.testBit d = true := by
          rcases hdb with ⟨rfl, _⟩ | ⟨_, rfl⟩ <;> (first | exact hp' | exact hq')
        have hex7 : getExactDegStrict deg cur i = 7 := by rw [hsp_ex (Or.inr (Or.inl hd_b)), hk7]
        rcases hind_i.2.2.2.2 (by omega) with ⟨hex5, _⟩ | ⟨hex6, _⟩ | ⟨_, _, _, _, _, h_db⟩ | ⟨hex8, _⟩ <;>
          try omega
        exact hl hdb h_db
      · have h_in := hind_in.2.2.1; rw [hnh] at h_in; rw [Nat.add_comm i deg] at h_in
        exact hl hib h_in
    · rcases hk8c with hac | hci | hcd | hdi | hed | hei | heb | hib
      · have hcv : usedMask.testBit cv = true := by
          rcases hac with ⟨_, rfl⟩ | ⟨rfl, _⟩ <;> (first | exact hq' | exact hp')
        have hex8 : getExactDegStrict deg cur i = 8 := by rw [hsp_ex (Or.inl hcv), hk8]
        rcases hind_i.2.2.2.2 (by omega) with ⟨hex5, _⟩ | ⟨hex6, _⟩ | ⟨hex7, _⟩ | ⟨_, h_ac, _⟩ <;>
          try omega
        rw [ha_comm] at h_ac; exact hl hac h_ac
      · have hcv : usedMask.testBit cv = true := by
          rcases hci with ⟨rfl, _⟩ | ⟨_, rfl⟩ <;> (first | exact hp' | exact hq')
        have hex8 : getExactDegStrict deg cur i = 8 := by rw [hsp_ex (Or.inl hcv), hk8]
        rcases hind_i.2.2.2.2 (by omega) with ⟨hex5, _⟩ | ⟨hex6, _⟩ | ⟨hex7, _⟩ | ⟨_, _, h_ci, _⟩ <;>
          try omega
        exact hl hci h_ci
      · have hd_b : usedMask.testBit d = true := by
          rcases hcd with ⟨_, rfl⟩ | ⟨rfl, _⟩ <;> (first | exact hq' | exact hp')
        have hex8 : getExactDegStrict deg cur i = 8 := by rw [hsp_ex (Or.inr (Or.inl hd_b)), hk8]
        rcases hind_i.2.2.2.2 (by omega) with ⟨hex5, _⟩ | ⟨hex6, _⟩ | ⟨hex7, _⟩ | ⟨_, _, _, h_cd, _⟩ <;>
          try omega
        exact hl hcd h_cd
      · have hd_b : usedMask.testBit d = true := by
          rcases hdi with ⟨rfl, _⟩ | ⟨_, rfl⟩ <;> (first | exact hp' | exact hq')
        have hex8 : getExactDegStrict deg cur i = 8 := by rw [hsp_ex (Or.inr (Or.inl hd_b)), hk8]
        rcases hind_i.2.2.2.2 (by omega) with ⟨hex5, _⟩ | ⟨hex6, _⟩ | ⟨hex7, _⟩ | ⟨_, _, _, _, h_di, _⟩ <;>
          try omega
        exact hl hdi h_di
      · have he_b : usedMask.testBit e = true := by
          rcases hed with ⟨rfl, _⟩ | ⟨_, rfl⟩ <;> (first | exact hp' | exact hq')
        have hex8 : getExactDegStrict deg cur i = 8 := by rw [hsp_ex (Or.inr (Or.inr he_b)), hk8]
        rcases hind_i.2.2.2.2 (by omega) with ⟨hex5, _⟩ | ⟨hex6, _⟩ | ⟨hex7, _⟩ | ⟨_, _, _, _, _, h_ed, _⟩ <;>
          try omega
        exact hl hed h_ed
      · have he_b : usedMask.testBit e = true := by
          rcases hei with ⟨rfl, _⟩ | ⟨_, rfl⟩ <;> (first | exact hp' | exact hq')
        have hex8 : getExactDegStrict deg cur i = 8 := by rw [hsp_ex (Or.inr (Or.inr he_b)), hk8]
        rcases hind_i.2.2.2.2 (by omega) with ⟨hex5, _⟩ | ⟨hex6, _⟩ | ⟨hex7, _⟩ | ⟨_, _, _, _, _, _, h_ei, _⟩ <;>
          try omega
        exact hl hei h_ei
      · have he_b : usedMask.testBit e = true := by
          rcases heb with ⟨rfl, _⟩ | ⟨_, rfl⟩ <;> (first | exact hp' | exact hq')
        have hex8 : getExactDegStrict deg cur i = 8 := by rw [hsp_ex (Or.inr (Or.inr he_b)), hk8]
        rcases hind_i.2.2.2.2 (by omega) with ⟨hex5, _⟩ | ⟨hex6, _⟩ | ⟨hex7, _⟩ | ⟨_, _, _, _, _, _, _, h_eb⟩ <;>
          try omega
        exact hl heb h_eb
      · have h_in := hind_in.2.2.1; rw [hnh] at h_in; rw [Nat.add_comm i deg] at h_in
        exact hl hib h_in
  rcases hdir with hne | hne
  · exact hstep hp hq (Or.inl ⟨rfl, rfl⟩) hne
  · exact hstep hq hp (Or.inr ⟨rfl, rfl⟩) hne

private theorem spokeTriSpecs_distinct (T : Hypermap) {deg : Nat} (hdeg5 : 5 ≤ deg)
    (hdeg11 : deg ≤ 11) (refl : Bool) (d0 : T.Dart) {i k x y z : Nat} {gen : T.Dart}
    (hi1 : 1 ≤ i) (hi_deg : i ≤ deg)
    (hmem : (x, y, z, gen) ∈ spokeTriSpecs T deg refl d0 i k) :
    x < 63 ∧ y < 63 ∧ z < 63 ∧ x ≠ y ∧ y ≠ z ∧ x ≠ z := by
  dsimp only [spokeTriSpecs] at hmem
  by_cases hi1' : i = 1
  · subst hi1'
    simp only [reduceIte] at hmem
    by_cases hk5 : k = 5
    · rw [if_pos hk5] at hmem
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
        Prod.mk.injEq] at hmem
      rcases hmem with (⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩) | ⟨rfl, rfl, rfl, _⟩ <;> omega
    · rw [if_neg hk5] at hmem
      by_cases hk6 : k = 6
      · rw [if_pos hk6] at hmem
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
          Prod.mk.injEq] at hmem
        rcases hmem with (⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩) |
          (⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩) <;> omega
      · rw [if_neg hk6] at hmem
        by_cases hk7 : k = 7
        · rw [if_pos hk7] at hmem
          simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
            Prod.mk.injEq] at hmem
          rcases hmem with (⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩) |
            (⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩) <;> omega
        · rw [if_neg hk7] at hmem
          by_cases hk8 : k = 8
          · rw [if_pos hk8] at hmem
            simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
              Prod.mk.injEq] at hmem
            rcases hmem with (⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩) |
              (⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩) <;>
              omega
          · rw [if_neg hk8] at hmem
            simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
            rcases hmem with ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ <;> omega
  · rw [if_neg hi1'] at hmem
    by_cases hk5 : k = 5
    · rw [if_pos hk5] at hmem
      simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
        Prod.mk.injEq] at hmem
      rcases hmem with (⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩) | ⟨rfl, rfl, rfl, _⟩ <;> omega
    · rw [if_neg hk5] at hmem
      by_cases hk6 : k = 6
      · rw [if_pos hk6] at hmem
        simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
          Prod.mk.injEq] at hmem
        rcases hmem with (⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩) |
          (⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩) <;> omega
      · rw [if_neg hk6] at hmem
        by_cases hk7 : k = 7
        · rw [if_pos hk7] at hmem
          simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
            Prod.mk.injEq] at hmem
          rcases hmem with (⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩) |
            (⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩) <;> omega
        · rw [if_neg hk7] at hmem
          by_cases hk8 : k = 8
          · rw [if_pos hk8] at hmem
            simp only [List.mem_cons, List.mem_append, List.not_mem_nil, or_false,
              Prod.mk.injEq] at hmem
            rcases hmem with (⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩) |
              (⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩) <;>
              omega
          · rw [if_neg hk8] at hmem
            simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
            rcases hmem with ⟨rfl, rfl, rfl, _⟩ | ⟨rfl, rfl, rfl, _⟩ <;> omega

private theorem not_beq63_of_ne {x : Nat} (hx : x ≠ 63) : (!(x == 63)) = true := by
  have hbe : (x == 63) = false := Bool.eq_false_iff.mpr fun h => hx (eq_of_beq h)
  simp [hbe]

private theorem cartAdjSpokeStrict_tri_of_three_in_mask {h : Nat} (_hh : h < 633)
    {T : Hypermap} [DecidableEq T.Dart] {fuel : Nat} (refl : Bool) (d0 : T.Dart)
    {cur img usedMask : Nat}
    (hdeg5 : 5 ≤ Math.Hypermap.nodeDegree T d0 fuel)
    (hmin5 : ∀ r, 1 ≤ r → r ≤ 5 * Math.Hypermap.nodeDegree T d0 fuel →
      5 ≤ cartDegOriented T fuel (Math.Hypermap.nodeDegree T d0 fuel) refl d0 r)
    (hmask_iff : ∀ k, usedMask.testBit k = true ↔
      ∃ iv ∈ (lookupFastConfRec h).intVerts, getImgNat img iv.u = k)
    (hexact : ∀ iv ∈ (lookupFastConfRec h).intVerts,
      getImgNat img iv.u ≤ 5 * Math.Hypermap.nodeDegree T d0 fuel ∧
      iv.d = getUppStrict (Math.Hypermap.nodeDegree T d0 fuel) cur (getImgNat img iv.u) ∧
      cartDegOriented T fuel (Math.Hypermap.nodeDegree T d0 fuel) refl d0 (getImgNat img iv.u) = iv.d)
    {i u v w : Nat} (hi1 : 1 ≤ i) (hi_deg : i ≤ Math.Hypermap.nodeDegree T d0 fuel)
    (hu : usedMask.testBit u = true) (hv : usedMask.testBit v = true)
    (hwm : usedMask.testBit w = true)
    (hadj : cartAdjSpokeStrict (Math.Hypermap.nodeDegree T d0 fuel) cur i u v = w)
    (hw63 : w ≠ 63) :
    ∃ x y z gen,
      (x, y, z, gen) ∈ spokeTriSpecs T (Math.Hypermap.nodeDegree T d0 fuel) refl d0 i
        (cartDegOriented T fuel (Math.Hypermap.nodeDegree T d0 fuel) refl d0 i) ∧
      pureTriAdj x y z u v = w := by
  let deg := Math.Hypermap.nodeDegree T d0 fuel
  let cd := cartDegOriented T fuel deg refl d0
  let hs := if i = 1 then deg else i - 1
  have hbase1 : ∃ gen, (0, hs, i, gen) ∈ spokeTriSpecs T deg refl d0 i (cd i) := by
    dsimp only [spokeTriSpecs]
    have hhs : (if i = 1 then deg else i - 1) = hs := rfl
    rw [hhs]
    split
    · exact ⟨spokeDartOriented T refl d0 hs, by simp⟩
    · split
      · exact ⟨spokeDartOriented T refl d0 hs, by simp⟩
      · split
        · exact ⟨spokeDartOriented T refl d0 hs, by simp⟩
        · split
          · exact ⟨spokeDartOriented T refl d0 hs, by simp⟩
          · exact ⟨spokeDartOriented T refl d0 hs, by simp⟩
  have hbase2 : ∃ gen, (i, hs, deg + hs, gen) ∈ spokeTriSpecs T deg refl d0 i (cd i) := by
    dsimp only [spokeTriSpecs]
    have hhs : (if i = 1 then deg else i - 1) = hs := rfl
    rw [hhs]
    split
    · exact ⟨(nodePermOriented T refl).f (T.edge.f (spokeDartOriented T refl d0 i)), by simp⟩
    · split
      · exact ⟨(nodePermOriented T refl).f (T.edge.f (spokeDartOriented T refl d0 i)), by simp⟩
      · split
        · exact ⟨(nodePermOriented T refl).f (T.edge.f (spokeDartOriented T refl d0 i)), by simp⟩
        · split
          · exact ⟨(nodePermOriented T refl).f (T.edge.f (spokeDartOriented T refl d0 i)), by simp⟩
          · exact ⟨(nodePermOriented T refl).f (T.edge.f (spokeDartOriented T refl d0 i)), by simp⟩
  have hk_from_i_tri : ∀ {y z : Nat}, pureTriAdj i y z u v = w → cd i = getUppStrict deg cur i := by
    intro y z hpt
    have hi_mask : usedMask.testBit i = true := by
      rcases pureTriAdj_elems hw63 hpt with ⟨rfl, _, _⟩ | ⟨_, _, rfl⟩ | ⟨_, rfl, _⟩
      · exact hu
      · exact hwm
      · exact hv
    rcases (hmask_iff i).mp hi_mask with ⟨iv, hiv, hiu⟩
    have ⟨_, hdupp, hdcd⟩ := hexact iv hiv
    rw [hiu] at hdupp hdcd
    exact hdcd.trans hdupp
  dsimp only [cartAdjSpokeStrict] at hadj
  simp only [strictNat_eq, bool_rec_eq, fanTri63Strict_eq_pureTriAdj, nat_beq_eq,
    Nat.add_eq, Nat.sub_eq, Nat.mul_eq] at hadj
  have hdeg_rw : Math.Hypermap.nodeDegree T d0 fuel = deg := rfl
  rw [hdeg_rw] at hadj
  have hhs_beq : (if (i == 1) = true then deg else i - 1) = hs := by
    dsimp only [hs]; simp only [beq_iff_eq]
  rw [hhs_beq] at hadj
  by_cases hr1 : pureTriAdj 0 hs i u v = 63
  · rw [hr1, if_neg (by decide)] at hadj
    by_cases hr2 : pureTriAdj i hs (deg + hs) u v = 63
    · rw [hr2, if_neg (by decide)] at hadj
      by_cases h9 : Nat.ble 9 (getUppStrict deg cur i) = true
      · simp only [h9, ↓reduceIte] at hadj
        exact absurd hadj.symm hw63
      · have h9f : Nat.ble 9 (getUppStrict deg cur i) = false := Bool.eq_false_iff.mpr h9
        simp only [h9f, Bool.false_eq_true, ↓reduceIte] at hadj
        by_cases hk5 : (getUppStrict deg cur i == 5) = true
        · simp only [hk5, ↓reduceIte] at hadj
          have hcd_eq : cd i = 5 := (hk_from_i_tri hadj).trans (eq_of_beq hk5)
          have hgen : ∃ gen, (i, deg + hs, deg + i, gen) ∈ spokeTriSpecs T deg refl d0 i (cd i) := by
            dsimp only [spokeTriSpecs]
            rw [hcd_eq, if_pos rfl]
            have hhs2 : (if i = 1 then deg else i - 1) = hs := rfl
            rw [hhs2]
            exact ⟨_, List.mem_append_right _ List.mem_cons_self⟩
          rcases hgen with ⟨gen, hmem⟩
          exact ⟨i, deg + hs, deg + i, gen, hmem, hadj⟩
        · have hk5f : (getUppStrict deg cur i == 5) = false := Bool.eq_false_iff.mpr hk5
          simp only [hk5f, Bool.false_eq_true, ↓reduceIte] at hadj
          by_cases hr3 : pureTriAdj i (deg + hs) (2 * deg + i) u v = 63
          · rw [hr3, if_neg (by decide)] at hadj
            by_cases hk6 : (getUppStrict deg cur i == 6) = true
            · simp only [hk6, ↓reduceIte] at hadj
              have hcd_eq : cd i = 6 := (hk_from_i_tri hadj).trans (eq_of_beq hk6)
              have hgen : ∃ gen, (i, 2 * deg + i, deg + i, gen) ∈ spokeTriSpecs T deg refl d0 i (cd i) := by
                dsimp only [spokeTriSpecs]
                rw [hcd_eq, if_neg (by decide), if_pos rfl]
                exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
              rcases hgen with ⟨gen, hmem⟩
              exact ⟨i, 2 * deg + i, deg + i, gen, hmem, hadj⟩
            · have hk6f : (getUppStrict deg cur i == 6) = false := Bool.eq_false_iff.mpr hk6
              simp only [hk6f, Bool.false_eq_true, ↓reduceIte] at hadj
              by_cases hr4 : pureTriAdj i (2 * deg + i) (3 * deg + i) u v = 63
              · rw [hr4, if_neg (by decide)] at hadj
                by_cases hk7 : (getUppStrict deg cur i == 7) = true
                · simp only [hk7, ↓reduceIte] at hadj
                  have hcd_eq : cd i = 7 := (hk_from_i_tri hadj).trans (eq_of_beq hk7)
                  have hgen : ∃ gen, (i, 3 * deg + i, deg + i, gen) ∈ spokeTriSpecs T deg refl d0 i (cd i) := by
                    dsimp only [spokeTriSpecs]
                    rw [hcd_eq, if_neg (by decide), if_neg (by decide), if_pos rfl]
                    exact ⟨_, List.mem_append_right _
                      (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩
                  rcases hgen with ⟨gen, hmem⟩
                  exact ⟨i, 3 * deg + i, deg + i, gen, hmem, hadj⟩
                · have hk7f : (getUppStrict deg cur i == 7) = false := Bool.eq_false_iff.mpr hk7
                  simp only [hk7f, Bool.false_eq_true, ↓reduceIte] at hadj
                  by_cases hr5 : pureTriAdj i (3 * deg + i) (4 * deg + i) u v = 63
                  · rw [hr5, if_neg (by decide)] at hadj
                    have hcd_eq' : cd i = getUppStrict deg cur i := hk_from_i_tri hadj
                    have hcd5 : 5 ≤ cd i := hmin5 i hi1 (by omega)
                    have hlt9 : ¬ 9 ≤ getUppStrict deg cur i := fun hle =>
                      h9 (Nat.ble_eq.mpr hle)
                    have hne5 : getUppStrict deg cur i ≠ 5 := fun he => hk5 (beq_iff_eq.mpr he)
                    have hne6 : getUppStrict deg cur i ≠ 6 := fun he => hk6 (beq_iff_eq.mpr he)
                    have hne7 : getUppStrict deg cur i ≠ 7 := fun he => hk7 (beq_iff_eq.mpr he)
                    have hk8 : getUppStrict deg cur i = 8 := by omega
                    have hcd8 : cd i = 8 := hcd_eq'.trans hk8
                    have hgen : ∃ gen, (i, 4 * deg + i, deg + i, gen) ∈ spokeTriSpecs T deg refl d0 i (cd i) := by
                      dsimp only [spokeTriSpecs]
                      rw [hcd8, if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
                      exact ⟨_, List.mem_append_right _
                        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                          (List.mem_cons_of_mem _ List.mem_cons_self)))⟩
                    rcases hgen with ⟨gen, hmem⟩
                    exact ⟨i, 4 * deg + i, deg + i, gen, hmem, hadj⟩
                  · rw [if_pos (not_beq63_of_ne hr5)] at hadj
                    have hcd_eq' : cd i = getUppStrict deg cur i := hk_from_i_tri hadj
                    have hcd5 : 5 ≤ cd i := hmin5 i hi1 (by omega)
                    have hlt9 : ¬ 9 ≤ getUppStrict deg cur i := fun hle =>
                      h9 (Nat.ble_eq.mpr hle)
                    have hne5 : getUppStrict deg cur i ≠ 5 := fun he => hk5 (beq_iff_eq.mpr he)
                    have hne6 : getUppStrict deg cur i ≠ 6 := fun he => hk6 (beq_iff_eq.mpr he)
                    have hne7 : getUppStrict deg cur i ≠ 7 := fun he => hk7 (beq_iff_eq.mpr he)
                    have hk8 : getUppStrict deg cur i = 8 := by omega
                    have hcd8 : cd i = 8 := hcd_eq'.trans hk8
                    have hgen : ∃ gen, (i, 3 * deg + i, 4 * deg + i, gen) ∈ spokeTriSpecs T deg refl d0 i (cd i) := by
                      dsimp only [spokeTriSpecs]
                      rw [hcd8, if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
                      exact ⟨_, List.mem_append_right _
                        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))⟩
                    rcases hgen with ⟨gen, hmem⟩
                    exact ⟨i, 3 * deg + i, 4 * deg + i, gen, hmem, hadj⟩
              · rw [if_pos (not_beq63_of_ne hr4)] at hadj
                have hcd_eq' : cd i = getUppStrict deg cur i := hk_from_i_tri hadj
                have hcd5 : 5 ≤ cd i := hmin5 i hi1 (by omega)
                have hlt9 : ¬ 9 ≤ getUppStrict deg cur i := fun hle => h9 (Nat.ble_eq.mpr hle)
                have hne5 : getUppStrict deg cur i ≠ 5 := fun he => hk5 (beq_iff_eq.mpr he)
                have hne6 : getUppStrict deg cur i ≠ 6 := fun he => hk6 (beq_iff_eq.mpr he)
                have h78 : getUppStrict deg cur i = 7 ∨ getUppStrict deg cur i = 8 := by omega
                rcases h78 with hk7 | hk8
                · have hcd7 : cd i = 7 := hcd_eq'.trans hk7
                  have hgen : ∃ gen, (i, 2 * deg + i, 3 * deg + i, gen) ∈ spokeTriSpecs T deg refl d0 i (cd i) := by
                    dsimp only [spokeTriSpecs]
                    rw [hcd7, if_neg (by decide), if_neg (by decide), if_pos rfl]
                    exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
                  rcases hgen with ⟨gen, hmem⟩
                  exact ⟨i, 2 * deg + i, 3 * deg + i, gen, hmem, hadj⟩
                · have hcd8 : cd i = 8 := hcd_eq'.trans hk8
                  have hgen : ∃ gen, (i, 2 * deg + i, 3 * deg + i, gen) ∈ spokeTriSpecs T deg refl d0 i (cd i) := by
                    dsimp only [spokeTriSpecs]
                    rw [hcd8, if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
                    exact ⟨_, List.mem_append_right _ (List.mem_cons_of_mem _ List.mem_cons_self)⟩
                  rcases hgen with ⟨gen, hmem⟩
                  exact ⟨i, 2 * deg + i, 3 * deg + i, gen, hmem, hadj⟩
          · rw [if_pos (not_beq63_of_ne hr3)] at hadj
            have hcd_eq' : cd i = getUppStrict deg cur i := hk_from_i_tri hadj
            have hcd5 : 5 ≤ cd i := hmin5 i hi1 (by omega)
            have hlt9 : ¬ 9 ≤ getUppStrict deg cur i := fun hle => h9 (Nat.ble_eq.mpr hle)
            have hne5 : getUppStrict deg cur i ≠ 5 := fun he => hk5 (beq_iff_eq.mpr he)
            have h678 : getUppStrict deg cur i = 6 ∨ getUppStrict deg cur i = 7 ∨
                getUppStrict deg cur i = 8 := by omega
            have hhs2 : (if i = 1 then deg else i - 1) = hs := rfl
            rcases h678 with hk6 | hk7 | hk8
            · have hcd6 : cd i = 6 := hcd_eq'.trans hk6
              have hgen : ∃ gen, (i, deg + hs, 2 * deg + i, gen) ∈ spokeTriSpecs T deg refl d0 i (cd i) := by
                dsimp only [spokeTriSpecs]; rw [hcd6, hhs2, if_neg (by decide), if_pos rfl]
                exact ⟨_, List.mem_append_right _ List.mem_cons_self⟩
              rcases hgen with ⟨gen, hmem⟩
              exact ⟨i, deg + hs, 2 * deg + i, gen, hmem, hadj⟩
            · have hcd7 : cd i = 7 := hcd_eq'.trans hk7
              have hgen : ∃ gen, (i, deg + hs, 2 * deg + i, gen) ∈ spokeTriSpecs T deg refl d0 i (cd i) := by
                dsimp only [spokeTriSpecs]
                rw [hcd7, hhs2, if_neg (by decide), if_neg (by decide), if_pos rfl]
                exact ⟨_, List.mem_append_right _ List.mem_cons_self⟩
              rcases hgen with ⟨gen, hmem⟩
              exact ⟨i, deg + hs, 2 * deg + i, gen, hmem, hadj⟩
            · have hcd8 : cd i = 8 := hcd_eq'.trans hk8
              have hgen : ∃ gen, (i, deg + hs, 2 * deg + i, gen) ∈ spokeTriSpecs T deg refl d0 i (cd i) := by
                dsimp only [spokeTriSpecs]
                rw [hcd8, hhs2, if_neg (by decide), if_neg (by decide), if_neg (by decide), if_pos rfl]
                exact ⟨_, List.mem_append_right _ List.mem_cons_self⟩
              rcases hgen with ⟨gen, hmem⟩
              exact ⟨i, deg + hs, 2 * deg + i, gen, hmem, hadj⟩
    · rw [if_pos (not_beq63_of_ne hr2)] at hadj
      rcases hbase2 with ⟨gen, hmem⟩
      exact ⟨i, hs, deg + hs, gen, hmem, hadj⟩
  · rw [if_pos (not_beq63_of_ne hr1)] at hadj
    rcases hbase1 with ⟨gen, hmem⟩
    exact ⟨0, hs, i, gen, hmem, hadj⟩

private theorem cartAdjStrict_tri_of_three_in_mask {h : Nat} (hh : h < 633)
    {T : Hypermap} [DecidableEq T.Dart] {fuel : Nat} (refl : Bool) (d0 : T.Dart)
    {cur img usedMask : Nat}
    (hdeg5 : 5 ≤ Math.Hypermap.nodeDegree T d0 fuel)
    (hmin5 : ∀ r, 1 ≤ r → r ≤ 5 * Math.Hypermap.nodeDegree T d0 fuel →
      5 ≤ cartDegOriented T fuel (Math.Hypermap.nodeDegree T d0 fuel) refl d0 r)
    (hmask_iff : ∀ k, usedMask.testBit k = true ↔
      ∃ iv ∈ (lookupFastConfRec h).intVerts, getImgNat img iv.u = k)
    (hexact : ∀ iv ∈ (lookupFastConfRec h).intVerts,
      getImgNat img iv.u ≤ 5 * Math.Hypermap.nodeDegree T d0 fuel ∧
      iv.d = getUppStrict (Math.Hypermap.nodeDegree T d0 fuel) cur (getImgNat img iv.u) ∧
      cartDegOriented T fuel (Math.Hypermap.nodeDegree T d0 fuel) refl d0 (getImgNat img iv.u) = iv.d)
    {u v w : Nat}
    (hu : usedMask.testBit u = true) (hv : usedMask.testBit v = true)
    (hwm : usedMask.testBit w = true)
    (hadj : cartAdjStrict (Math.Hypermap.nodeDegree T d0 fuel) cur u v = w)
    (hw63 : w ≠ 63) :
    ∃ i' x y z gen,
      1 ≤ i' ∧ i' ≤ Math.Hypermap.nodeDegree T d0 fuel ∧
      (x, y, z, gen) ∈ spokeTriSpecs T (Math.Hypermap.nodeDegree T d0 fuel) refl d0 i'
        (cartDegOriented T fuel (Math.Hypermap.nodeDegree T d0 fuel) refl d0 i') ∧
      pureTriAdj x y z u v = w := by
  let deg := Math.Hypermap.nodeDegree T d0 fuel
  let cd := cartDegOriented T fuel deg refl d0
  dsimp only [cartAdjStrict] at hadj
  simp only [strictNat_eq, bool_rec_eq, nat_beq_eq, Nat.add_eq, Nat.sub_eq] at hadj
  have hdeg_rw : Math.Hypermap.nodeDegree T d0 fuel = deg := rfl
  rw [hdeg_rw] at hadj
  by_cases hu0 : (u == 0) = true
  · have hu_eq : u = 0 := eq_of_beq hu0
    simp only [hu0, ↓reduceIte] at hadj
    by_cases hvb : (Nat.ble 1 v && v.ble deg) = true
    · rw [if_pos hvb] at hadj
      have ⟨hv1b, hvdb⟩ := (Bool.and_eq_true _ _).mp hvb
      have hv1 : 1 ≤ v := Nat.ble_eq.mp hv1b
      have hv_deg : v ≤ deg := Nat.ble_eq.mp hvdb
      have hi1 : 1 ≤ w := by by_cases hvd : v = deg <;> simp [hvd] at hadj <;> omega
      have hi_deg : w ≤ deg := by by_cases hvd : v = deg <;> simp [hvd] at hadj <;> omega
      have hw_prev : (if w = 1 then deg else w - 1) = v := by
        by_cases hvd : v = deg
        · subst hvd; simp only [beq_self_eq_true, ↓reduceIte] at hadj; subst hadj; rfl
        · have hvb_f : (v == deg) = false := Bool.eq_false_iff.mpr fun h => hvd (eq_of_beq h)
          simp only [hvb_f, Bool.false_eq_true, ↓reduceIte] at hadj
          subst hadj
          have hne1 : v + 1 ≠ 1 := by omega
          rw [if_neg hne1]
          omega
      have hbase : ∃ gen, (0, v, w, gen) ∈ spokeTriSpecs T deg refl d0 w (cd w) := by
        dsimp only [spokeTriSpecs]
        rw [hw_prev]
        split
        · exact ⟨spokeDartOriented T refl d0 v, by simp⟩
        · split
          · exact ⟨spokeDartOriented T refl d0 v, by simp⟩
          · split
            · exact ⟨spokeDartOriented T refl d0 v, by simp⟩
            · split
              · exact ⟨spokeDartOriented T refl d0 v, by simp⟩
              · exact ⟨spokeDartOriented T refl d0 v, by simp⟩
      rcases hbase with ⟨gen, hmem⟩
      refine ⟨w, 0, v, w, gen, hi1, hi_deg, hmem, ?_⟩
      dsimp only [pureTriAdj]
      subst hu_eq
      simp
    · rw [if_neg hvb] at hadj
      exact absurd hadj.symm hw63
  · have hu0f : (u == 0) = false := Bool.eq_false_iff.mpr hu0
    simp only [hu0f, Bool.false_eq_true, ↓reduceIte] at hadj
    let i1 := (u - 1) % deg + 1
    have hi1_rw : (u - 1).mod deg + 1 = i1 := rfl
    rw [hi1_rw] at hadj
    have hi1_1 : 1 ≤ i1 := by dsimp only [i1]; omega
    have hi1_deg : i1 ≤ deg := by
      dsimp only [i1]
      have := Nat.mod_lt (u - 1) (by omega : 0 < deg)
      omega
    by_cases hw1 : cartAdjSpokeStrict deg cur i1 u v = 63
    · rw [hw1, if_neg (by decide)] at hadj
      let i2 := if i1 = deg then 1 else i1 + 1
      have hi2_1 : 1 ≤ i2 := by dsimp only [i2]; split <;> omega
      have hi2_deg : i2 ≤ deg := by dsimp only [i2]; split <;> omega
      have hite : (if (i1 == deg) = true then 1 else i1 + 1) = i2 := by
        dsimp only [i2]; simp only [beq_iff_eq]
      rw [hite] at hadj
      rcases cartAdjSpokeStrict_tri_of_three_in_mask hh refl d0 hdeg5 hmin5 hmask_iff hexact
        hi2_1 hi2_deg hu hv hwm hadj hw63 with ⟨x, y, z, gen, hmem, hpt⟩
      exact ⟨i2, x, y, z, gen, hi2_1, hi2_deg, hmem, hpt⟩
    · rw [if_pos (not_beq63_of_ne hw1)] at hadj
      rcases cartAdjSpokeStrict_tri_of_three_in_mask hh refl d0 hdeg5 hmin5 hmask_iff hexact
        hi1_1 hi1_deg hu hv hwm hadj hw63 with ⟨x, y, z, gen, hmem, hpt⟩
      exact ⟨i1, x, y, z, gen, hi1_1, hi1_deg, hmem, hpt⟩

private theorem checkVertCycRec_cons (deg ring st img : Nat) (cw : Bool) (fu : Nat)
    (cpv cpw : Nat) (tl : List CycPair) (worried : Bool) :
    checkVertCycRec deg ring st img cw fu ({ v := cpv, w := cpw } :: tl) worried =
      if cpv.ble ring = true then checkVertCycRec deg ring st img cw fu tl true
      else if cpw.ble ring = true then
        if worried = true then false else checkVertCycRec deg ring st img cw fu tl worried
      else if (cartAdjStrict deg st (if cw = true then fu else getImgNat img cpv)
          (if cw = true then getImgNat img cpv else fu)).beq (getImgNat img cpw) = true then
        checkVertCycRec deg ring st img cw fu tl false
      else false := by
  generalize hb1 : cpv.ble ring = b1
  cases b1
  · generalize hfv : getImgNat img cpv = fv
    cases fv <;>
    · generalize hb2 : cpw.ble ring = b2
      cases b2
      · cases cw <;>
        · generalize hb3 : (cartAdjStrict deg st _ _).beq (getImgNat img cpw) = b3
          cases b3 <;>
          · simp only [checkVertCycRec, hb1, hfv, hb2]
            rw [strictNat_eq]
            simp only [reduceIte, Bool.false_eq_true] at hb3
            simp [hb3]
      · cases cw <;> cases worried <;>
        · simp only [checkVertCycRec, hb1, hfv, hb2]
          rw [strictNat_eq]
          simp
  · simp [checkVertCycRec, hb1]

private theorem checkVertCycRec_sound (deg ring st img : Nat) (cw : Bool) (fu : Nat) :
    ∀ (cps : List CycPair) (worried : Bool),
      checkVertCycRec deg ring st img cw fu cps worried = true →
      ∀ cp ∈ cps, ring < cp.v → ring < cp.w →
        cartAdjStrict deg st (if cw then fu else getImgNat img cp.v)
          (if cw then getImgNat img cp.v else fu) = getImgNat img cp.w := by
  intro cps worried hchk cp hmem hv hw
  induction cps generalizing worried with
  | nil => cases hmem
  | cons hd tl ih =>
    rcases hd with ⟨cpv, cpw⟩
    rw [checkVertCycRec_cons] at hchk
    by_cases hvb : cpv.ble ring = true
    · rw [if_pos hvb] at hchk
      rcases List.mem_cons.mp hmem with hhead | htl
      · rw [hhead] at hv
        have hle : cpv ≤ ring := Nat.ble_eq.mp hvb
        dsimp only at hv
        omega
      · exact ih true hchk htl
    · rw [if_neg hvb] at hchk
      by_cases hwb : cpw.ble ring = true
      · rw [if_pos hwb] at hchk
        rcases List.mem_cons.mp hmem with hhead | htl
        · rw [hhead] at hw
          have hle : cpw ≤ ring := Nat.ble_eq.mp hwb
          dsimp only at hw
          omega
        · by_cases hworr : worried = true
          · rw [if_pos hworr] at hchk
            cases hchk
          · have hworr_f : worried = false := Bool.eq_false_iff.mpr hworr
            rw [if_neg hworr] at hchk
            rw [hworr_f] at hchk
            exact ih false hchk htl
      · rw [if_neg hwb] at hchk
        by_cases htl_eq :
            (cartAdjStrict deg st (if cw = true then fu else getImgNat img cpv)
              (if cw = true then getImgNat img cpv else fu)).beq (getImgNat img cpw) = true
        · rw [if_pos htl_eq] at hchk
          rcases List.mem_cons.mp hmem with hhead | htl
          · rw [hhead]
            exact Nat.eq_of_beq_eq_true htl_eq
          · exact ih false hchk htl
        · rw [if_neg htl_eq] at hchk
          cases hchk

private theorem checkAllVertCycsRec_cons (deg ring st img : Nat) (cw : Bool)
    (hd : IntVert) (tl : List IntVert) :
    checkAllVertCycsRec deg ring st img cw (hd :: tl) =
      if checkVertCycRec deg ring st img cw (getImgNat img hd.u) hd.cyc hd.worried = true then
        checkAllVertCycsRec deg ring st img cw tl
      else false := by
  generalize hfu : getImgNat img hd.u = fu
  cases fu <;>
  · generalize hb : checkVertCycRec deg ring st img cw _ hd.cyc hd.worried = b
    cases b <;> simp [checkAllVertCycsRec, strictNat, hfu, hb]

private theorem checkAllVertCycsRec_sound (deg ring st img : Nat) (cw : Bool)
    (ivs : List IntVert) (hchk : checkAllVertCycsRec deg ring st img cw ivs = true) :
    ∀ iv ∈ ivs, ∀ cp ∈ iv.cyc, ring < cp.v → ring < cp.w →
      cartAdjStrict deg st (if cw then getImgNat img iv.u else getImgNat img cp.v)
        (if cw then getImgNat img cp.v else getImgNat img iv.u) = getImgNat img cp.w := by
  induction ivs with
  | nil => intro iv hmem; cases hmem
  | cons hd tl ih =>
    rw [checkAllVertCycsRec_cons] at hchk
    by_cases hhd : checkVertCycRec deg ring st img cw (getImgNat img hd.u) hd.cyc hd.worried = true
    · rw [if_pos hhd] at hchk
      intro iv hiv cp hcp hv hw
      rcases List.mem_cons.mp hiv with rfl | htl
      · exact checkVertCycRec_sound deg ring st img cw (getImgNat img iv.u)
          iv.cyc iv.worried hhd cp hcp hv hw
      · exact ih hchk iv htl cp hcp hv hw
    · rw [if_neg hhd] at hchk
      cases hchk

private theorem canonCartDart_step_of_cycPair {h : Nat} (hh : h < 633)
    {T : Hypermap} [DecidableEq T.Dart] (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    (h_tri : ∀ d : T.Dart, T.face.f (T.face.f (T.face.f d)) = d)
    (refl : Bool) (d0 : T.Dart)
    (hdeg5 : 5 ≤ Math.Hypermap.nodeDegree T d0 darts.length)
    (hdeg11 : Math.Hypermap.nodeDegree T d0 darts.length ≤ 11)
    (hmin5 : ∀ r, 1 ≤ r → r ≤ 5 * Math.Hypermap.nodeDegree T d0 darts.length →
      5 ≤ cartDegOriented T darts.length (Math.Hypermap.nodeDegree T d0 darts.length) refl d0 r)
    (hcw : CartwheelEmbedded T darts.length refl d0)
    {cur img usedMask : Nat} (cw : Bool)
    (hmask_iff : ∀ k, usedMask.testBit k = true ↔
      ∃ iv ∈ (lookupFastConfRec h).intVerts, getImgNat img iv.u = k)
    (hexact : ∀ iv ∈ (lookupFastConfRec h).intVerts,
      getImgNat img iv.u ≤ 5 * Math.Hypermap.nodeDegree T d0 darts.length ∧
      iv.d = getUppStrict (Math.Hypermap.nodeDegree T d0 darts.length) cur (getImgNat img iv.u) ∧
      cartDegOriented T darts.length (Math.Hypermap.nodeDegree T d0 darts.length) refl d0
        (getImgNat img iv.u) = iv.d)
    (hvert : checkAllVertCycsRec (Math.Hypermap.nodeDegree T d0 darts.length)
      (lookupFastConfRec h).ring cur img cw (lookupFastConfRec h).intVerts = true)
    (hlen : h < parsedRConfList.length := by rw [parsedRConfList_length]; exact hh)
    {iv ivv ivw : IntVert}
    (hiv : iv ∈ (lookupFastConfRec h).intVerts)
    (hivv : ivv ∈ (lookupFastConfRec h).intVerts)
    (hivw : ivw ∈ (lookupFastConfRec h).intVerts)
    {cp : CycPair} (hcp : cp ∈ iv.cyc)
    (huv_eq : ivv.u = cp.v) (huw_eq : ivw.u = cp.w) :
    let deg := Math.Hypermap.nodeDegree T d0 darts.length
    let cd := cartDegOriented T darts.length deg refl d0
    let fu := getImgNat img iv.u
    let fv := getImgNat img ivv.u
    let fw := getImgNat img ivw.u
    (∃ i1, 1 ≤ i1 ∧ i1 ≤ deg ∧ (spokeEdgeDart T deg refl d0 i1 (cd i1) fu fv).isSome = true) ∧
    (∃ i2, 1 ≤ i2 ∧ i2 ≤ deg ∧ (spokeEdgeDart T deg refl d0 i2 (cd i2) fu fw).isSome = true) ∧
    canonCartDart T deg refl d0 cd fu fw =
      (nodePermOriented T (if cw then refl else !refl)).f (canonCartDart T deg refl d0 cd fu fv) := by
  intro deg cd fu fv fw
  have hhdr := fastConf_equiv_header h hh
  have hivs := fastConf_equiv_intVerts h hh
  have hlen_ivs : (lookupFastConfRec h).intVerts.length = (configOfRConf (parsedRConfList[h]'hlen)).interiorSize :=
    hhdr.2.2.2.2.2.2.2.2.2.2.1
  have hring_eq : (lookupFastConfRec h).ring = (configOfRConf (parsedRConfList[h]'hlen)).ringSize := hhdr.1
  have hr_lt_v : (lookupFastConfRec h).ring < cp.v := by
    rcases List.mem_iff_getElem.mp hivv with ⟨jv, hjv, rfl⟩
    have hjv_c : jv < (configOfRConf (parsedRConfList[h]'hlen)).interiorSize := by
      rw [← hlen_ivs]; exact hjv
    have hv_eq := (hivs jv hjv_c).1
    omega
  have hr_lt_w : (lookupFastConfRec h).ring < cp.w := by
    rcases List.mem_iff_getElem.mp hivw with ⟨jw, hjw, rfl⟩
    have hjw_c : jw < (configOfRConf (parsedRConfList[h]'hlen)).interiorSize := by
      rw [← hlen_ivs]; exact hjw
    have hw_eq := (hivs jw hjw_c).1
    omega
  have hadj := checkAllVertCycsRec_sound deg (lookupFastConfRec h).ring cur img cw
    (lookupFastConfRec h).intVerts hvert iv hiv cp hcp hr_lt_v hr_lt_w
  rw [← huv_eq, ← huw_eq] at hadj
  change cartAdjStrict deg cur (if cw then fu else fv) (if cw then fv else fu) = fw at hadj
  have hmu : usedMask.testBit fu = true := (hmask_iff fu).mpr ⟨iv, hiv, rfl⟩
  have hmv : usedMask.testBit fv = true := (hmask_iff fv).mpr ⟨ivv, hivv, rfl⟩
  have hmw : usedMask.testBit fw = true := (hmask_iff fw).mpr ⟨ivw, hivw, rfl⟩
  have hfw63 : fw ≠ 63 := by have := (hexact ivw hivw).1; omega
  have hfv63 : fv ≠ 63 := by have := (hexact ivv hivv).1; omega
  by_cases hcw_b : cw = true
  · subst hcw_b
    simp only [reduceIte] at hadj ⊢
    rcases cartAdjStrict_tri_of_three_in_mask hh refl d0 hdeg5 hmin5 hmask_iff hexact
      hmu hmv hmw hadj hfw63 with ⟨i', x, y, z, gen, hi1, hi_deg, hmem, hpt⟩
    have hstep := canonCartDart_step_of_tri T darts h_all (Nat.le_refl _) h_tri refl d0
      hdeg5 hcw hi1 hi_deg hmem hpt hfw63
    exact ⟨⟨i', hi1, hi_deg, hstep.1⟩, ⟨i', hi1, hi_deg, hstep.2.1⟩, hstep.2.2⟩
  · have hcw_f : cw = false := Bool.eq_false_iff.mpr hcw_b
    subst hcw_f
    simp only [Bool.false_eq_true, reduceIte] at hadj ⊢
    rcases cartAdjStrict_tri_of_three_in_mask hh refl d0 hdeg5 hmin5 hmask_iff hexact
      hmv hmu hmw hadj hfw63 with ⟨i', x, y, z, gen, hi1, hi_deg, hmem, hpt⟩
    have hdist := spokeTriSpecs_distinct T hdeg5 hdeg11 refl d0 hi1 hi_deg hmem
    have hrot := (pureTriAdj_rot_left hpt hfw63 (Nat.ne_of_lt hdist.1) (Nat.ne_of_lt hdist.2.1)
      (Nat.ne_of_lt hdist.2.2.1) hdist.2.2.2.1 hdist.2.2.2.2.1 hdist.2.2.2.2.2).1
    have hstep := canonCartDart_step_of_tri T darts h_all (Nat.le_refl _) h_tri refl d0
      hdeg5 hcw hi1 hi_deg hmem hrot hfv63
    dsimp only [deg, cd]
    refine ⟨⟨i', hi1, hi_deg, hstep.2.1⟩, ⟨i', hi1, hi_deg, hstep.1⟩, ?_⟩
    have hinv_eq : (nodePermOriented T (!refl)).f = (nodePermOriented T refl).inv := by
      cases refl <;> rfl
    rw [hinv_eq]
    have hinv_step := congrArg (nodePermOriented T refl).inv hstep.2.2
    rw [Perm.left_inv] at hinv_step
    exact hinv_step.symm

private theorem areAdjacentVertices_of_tri_fan_turn {T : Hypermap} [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel)
    (h_tri : ∀ d : T.Dart, T.face.f (T.face.f (T.face.f d)) = d)
    (orient : Bool) {d1 d2 : T.Dart} (hd : d2 = (nodePermOriented T orient).f d1) :
    areAdjacentVertices T (T.edge.f d1) (T.edge.f d2) fuel = true := by
  have helper : ∀ {x y : T.Dart}, y = T.node.f x →
      areAdjacentVertices T (T.edge.f x) (T.edge.f y) fuel = true := by
    intro x y hxy
    rw [areAdjacentVertices_iff T darts h_all h_len]
    refine ⟨T.face.f x, ?_, ?_⟩
    · have hnd : T.node.f (T.face.f x) = T.edge.f x := by
        have h := congrArg T.edge.f (T.edge_node_face_id x)
        rw [T.edge_involution] at h
        exact h
      have hsv : sameVertex T (T.edge.f x) (T.face.f x) fuel = true := by
        rw [← hnd]
        exact sameVertex_node_f T darts h_all h_len (T.face.f x)
      rw [sameVertex_symm_of_complete T darts h_all h_len]
      exact hsv
    · have enf : ∀ z : T.Dart, T.node.f (T.face.f z) = T.edge.f z := fun z => by
        have h := congrArg T.edge.f (T.edge_node_face_id z)
        rw [T.edge_involution] at h
        exact h
      have henx : T.edge.f (T.node.f x) = T.face.f (T.face.f x) := by
        have h := T.edge_node_face_id (T.face.f (T.face.f x))
        rw [h_tri x] at h
        exact h
      have hnd : T.edge.f (T.face.f x) = T.node.f (T.edge.f y) := by
        rw [hxy, henx, enf (T.face.f x)]
      rw [hnd]
      exact sameVertex_node_f T darts h_all h_len (T.edge.f y)
  cases orient with
  | false => exact helper hd
  | true =>
    have hxy : d1 = T.node.f d2 := by
      dsimp only [nodePermOriented] at hd
      simp only [reduceIte] at hd
      rw [hd]
      exact (T.node.right_inv d1).symm
    rw [areAdjacentVertices_symm T darts h_all h_len]
    exact helper hxy

private def posInList (x : Nat) : List Nat → Nat
  | [] => 0
  | y :: ys => if x = y then 0 else posInList x ys + 1

private theorem posInList_lt {x : Nat} {l : List Nat} (hx : x ∈ l) : posInList x l < l.length := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [posInList, List.length_cons]
    by_cases hxy : x = y
    · simp [hxy]
    · simp only [hxy, ↓reduceIte]
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact absurd rfl hxy
      · exact Nat.succ_lt_succ (ih hmem)

private theorem getElem_posInList {x : Nat} {l : List Nat} (hx : x ∈ l) :
    l[posInList x l]'(posInList_lt hx) = x := by
  induction l with
  | nil => simp at hx
  | cons y ys ih =>
    simp only [posInList]
    by_cases hxy : x = y
    · subst hxy; simp
    · simp only [hxy, ↓reduceIte, List.getElem_cons_succ]
      rcases List.mem_cons.mp hx with rfl | hmem
      · exact absurd rfl hxy
      · exact ih hmem

private theorem posInList_getElem {l : List Nat} (hnd : l.Nodup) {i : Nat} (hi : i < l.length) :
    posInList (l[i]'hi) l = i := by
  induction l generalizing i with
  | nil => simp at hi
  | cons y ys ih =>
    rcases (List.nodup_cons.mp hnd) with ⟨hy, hys⟩
    cases i with
    | zero => simp [posInList]
    | succ j =>
      simp only [List.getElem_cons_succ, posInList]
      have hne : ys[j]'(Nat.lt_of_succ_lt_succ hi) ≠ y := fun he => hy (he ▸ List.getElem_mem _)
      simp [hne, ih hys (Nat.lt_of_succ_lt_succ hi)]

private theorem posInList_inj {l : List Nat} {x y : Nat} (hx : x ∈ l) (hy : y ∈ l)
    (heq : posInList x l = posInList y l) : x = y := by
  have hx' := getElem_posInList hx
  have hy' := getElem_posInList hy
  rw [← hx', ← hy']
  congr 1

private theorem rotateList_perm (l : List Nat) (k : Nat) : List.Perm (l.drop k ++ l.take k) l := by
  have h1 : List.Perm (l.drop k ++ l.take k) (l.take k ++ l.drop k) := List.perm_append_comm
  rw [List.take_append_drop] at h1
  exact h1

private theorem rotateList_nodup {l : List Nat} (hnd : l.Nodup) (k : Nat) :
    (l.drop k ++ l.take k).Nodup :=
  (rotateList_perm l k).nodup_iff.mpr hnd

private theorem rotateList_mem (l : List Nat) (k x : Nat) : x ∈ l.drop k ++ l.take k ↔ x ∈ l :=
  (rotateList_perm l k).mem_iff

private theorem rotateList_length (l : List Nat) (k : Nat) :
    (l.drop k ++ l.take k).length = l.length := by
  simp [List.length_append, List.length_drop, List.length_take]; omega

private theorem rotateList_getElem (l : List Nat) {k : Nat} (hk : k < l.length)
    {m : Nat} (hm : m < (l.drop k ++ l.take k).length) :
    (l.drop k ++ l.take k)[m]'hm =
      l[(k + m) % l.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hk)) := by
  have hlen : (l.drop k ++ l.take k).length = l.length := rotateList_length l k
  have hm_l : m < l.length := hlen ▸ hm
  have hdrop : (l.drop k).length = l.length - k := List.length_drop
  by_cases hlt : m < l.length - k
  · have hlt' : m < (l.drop k).length := hdrop ▸ hlt
    rw [List.getElem_append_left hlt', List.getElem_drop]
    congr 1
    rw [Nat.mod_eq_of_lt (by omega)]
  · have hge : (l.drop k).length ≤ m := by omega
    rw [List.getElem_append_right hge, List.getElem_take]
    congr 1
    have hmod : (k + m) % l.length = m - (l.length - k) := by
      have : k + m = (m - (l.length - k)) + l.length := by omega
      rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    rw [hdrop, hmod]

private theorem nodup_perm_of_mem_iff {α : Type} [DecidableEq α] {l1 l2 : List α}
    (h1 : l1.Nodup) (h2 : l2.Nodup) (hmem : ∀ x, x ∈ l1 ↔ x ∈ l2) : List.Perm l1 l2 := by
  induction l1 generalizing l2 with
  | nil =>
    cases l2 with
    | nil => exact .nil
    | cons a as => exact absurd ((hmem a).mpr (by simp)) (by simp)
  | cons a l1' ih =>
    rcases List.nodup_cons.mp h1 with ⟨ha1, h1'⟩
    have ha2 : a ∈ l2 := (hmem a).mp (by simp)
    have hperm2 : List.Perm l2 (a :: l2.erase a) := List.perm_cons_erase ha2
    have h2' : (l2.erase a).Nodup := (List.nodup_cons.mp (hperm2.nodup_iff.mp h2)).2
    have hmem' : ∀ x, x ∈ l1' ↔ x ∈ l2.erase a := by
      intro x
      constructor
      · intro hx
        have hne : x ≠ a := fun he => ha1 (he ▸ hx)
        exact (List.mem_erase_of_ne hne).mpr ((hmem x).mp (by simp [hx]))
      · intro hx
        have hne : x ≠ a := fun he => (List.nodup_cons.mp (hperm2.nodup_iff.mp h2)).1 (he ▸ hx)
        rcases List.mem_cons.mp ((hmem x).mpr (List.mem_of_mem_erase hx)) with rfl | hx1
        · exact absurd rfl hne
        · exact hx1
    exact (List.Perm.cons a (ih h1' h2' hmem')).trans hperm2.symm

private theorem countP_range_eq_length_of_nodup (n : Nat) (p : Nat → Bool) (l : List Nat)
    (hnd : l.Nodup) (hl : ∀ x ∈ l, x < n) (hp : ∀ y < n, p y = l.contains y) :
    (List.range n).countP p = l.length := by
  have h1 : (List.range n).countP p = (List.range n).countP (fun y => l.contains y) := by
    rw [List.countP_eq_length_filter, List.countP_eq_length_filter]
    congr 1
    apply List.filter_congr
    intro y hy
    exact hp y (List.mem_range.mp hy)
  rw [h1, List.countP_eq_length_filter]
  have hperm : List.Perm ((List.range n).filter (fun y => l.contains y)) l := by
    apply nodup_perm_of_mem_iff (List.nodup_range.sublist List.filter_sublist) hnd
    intro a
    simp only [List.mem_filter, List.mem_range, List.contains_eq_mem, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun ha => ⟨hl a ha, ha⟩⟩
  exact hperm.length_eq

end SWARAndIsoSoundness

section AppearsInTriangulation

def checkRingAdj (rc : FastReducer.RConf) : Bool :=
  let r := rc.r
  (List.range r).all fun x =>
    let adjx := (rc.adj.getD x #[]).toList
    (adjx.all fun y => decide (y < r) || ((adjx.drop 1).dropLast).contains y) &&
    (adjx.all fun y => decide (r ≤ y) || y == (x + 1) % r || x == (y + 1) % r)

private theorem ringAdj_row0 : rcTable[0]!.all (fun b => b.all checkRingAdj) = true := rfl
private theorem ringAdj_row1 : rcTable[1]!.all (fun b => b.all checkRingAdj) = true := rfl
private theorem ringAdj_row2 : rcTable[2]!.all (fun b => b.all checkRingAdj) = true := rfl
private theorem ringAdj_row3 : rcTable[3]!.all (fun b => b.all checkRingAdj) = true := rfl
private theorem ringAdj_row4 : rcTable[4]!.all (fun b => b.all checkRingAdj) = true := rfl
private theorem ringAdj_row5 : rcTable[5]!.all (fun b => b.all checkRingAdj) = true := rfl
private theorem ringAdj_row6 : rcTable[6]!.all (fun b => b.all checkRingAdj) = true := rfl
private theorem ringAdj_row7 : rcTable[7]!.all (fun b => b.all checkRingAdj) = true := rfl
private theorem ringAdj_row8 : rcTable[8]!.all (fun b => b.all checkRingAdj) = true := rfl
private theorem ringAdj_row9 : rcTable[9]!.all (fun b => b.all checkRingAdj) = true := rfl

private theorem ringAdj_row_of_lt (r0 : Nat) (hr0 : r0 < 10)
    (hr0' : r0 < rcTable.length := by rw [rcTable_len]; exact hr0) :
    (rcTable[r0]'hr0').all (fun b => b.all checkRingAdj) = true := by
  match r0 with
  | 0 => exact ringAdj_row0
  | 1 => exact ringAdj_row1
  | 2 => exact ringAdj_row2
  | 3 => exact ringAdj_row3
  | 4 => exact ringAdj_row4
  | 5 => exact ringAdj_row5
  | 6 => exact ringAdj_row6
  | 7 => exact ringAdj_row7
  | 8 => exact ringAdj_row8
  | 9 => exact ringAdj_row9
  | _ + 10 => omega

theorem fastConf_ringAdj (h : Nat) (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh) :
    checkRingAdj (parsedRConfList[h]'hlen) = true := by
  obtain ⟨hb0, hb1, hb2, heq⟩ := parsedRConfList_eq_table h hh
  have hrow : (rcTable[h >>> 6]'hb0).all (fun b => b.all checkRingAdj) = true :=
    ringAdj_row_of_lt (h >>> 6) (by rw [rcTable_len] at hb0; exact hb0) hb0
  have hb0_mem : rcTable[h >>> 6][((h >>> 3) &&& 7)]'hb1 ∈ rcTable[h >>> 6]'hb0 :=
    List.getElem_mem hb1
  have hcell : (rcTable[h >>> 6][((h >>> 3) &&& 7)]'hb1).all checkRingAdj = true :=
    (List.all_eq_true.mp hrow) _ hb0_mem
  have hb1_mem : ((rcTable[h >>> 6][((h >>> 3) &&& 7)]'hb1)[h &&& 7]'hb2) ∈
      rcTable[h >>> 6][((h >>> 3) &&& 7)]'hb1 :=
    List.getElem_mem hb2
  have hchk := (List.all_eq_true.mp hcell) _ hb1_mem
  simpa [heq] using hchk

private theorem array_getD_eq_getElem {α : Type} (xs : Array α) (d : α) (i : Nat) (hi : i < xs.size) :
    xs.getD i d = xs[i]'hi := by
  simp [Array.getD, hi]

private theorem ringAdj_int_in_fans {h : Nat} (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh) :
    let rc := parsedRConfList[h]'hlen
    ∀ x, x < rc.r → ∀ (hx_adj : x < rc.adj.size) y,
      y ∈ (rc.adj[x]'hx_adj).toList → rc.r ≤ y →
      y ∈ (((rc.adj[x]'hx_adj).toList.drop 1).dropLast) := by
  intro rc x hx hx_adj y hy hyr
  have hchk := fastConf_ringAdj h hh hlen
  dsimp [checkRingAdj] at hchk
  have hx_mem : x ∈ List.range rc.r := List.mem_range.mpr hx
  have hx_ok := (List.all_eq_true.mp hchk) x hx_mem
  rw [Bool.and_eq_true] at hx_ok
  have hy' : y ∈ (rc.adj.getD x #[]).toList := by rwa [array_getD_eq_getElem _ _ _ hx_adj]
  have hy_ok := (List.all_eq_true.mp hx_ok.1) y hy'
  rw [Bool.or_eq_true] at hy_ok
  rcases hy_ok with hy_lt | hy_in
  · have hy_lt' : y < rc.r := by simpa [decide_eq_true_eq] using hy_lt
    have hyr' : rc.r ≤ y := hyr
    omega
  · have hy_mem : y ∈ ((rc.adj.getD x #[]).toList.drop 1).dropLast := by
      simpa using hy_in
    rwa [array_getD_eq_getElem _ _ _ hx_adj] at hy_mem

private theorem ringAdj_consec {h : Nat} (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh) :
    let rc := parsedRConfList[h]'hlen
    ∀ x, x < rc.r → ∀ (hx_adj : x < rc.adj.size) y,
      y ∈ (rc.adj[x]'hx_adj).toList → y < rc.r →
      y = (x + 1) % rc.r ∨ x = (y + 1) % rc.r := by
  intro rc x hx hx_adj y hy hyr
  have hchk := fastConf_ringAdj h hh hlen
  dsimp [checkRingAdj] at hchk
  have hx_mem : x ∈ List.range rc.r := List.mem_range.mpr hx
  have hx_ok := (List.all_eq_true.mp hchk) x hx_mem
  rw [Bool.and_eq_true] at hx_ok
  have hy' : y ∈ (rc.adj.getD x #[]).toList := by rwa [array_getD_eq_getElem _ _ _ hx_adj]
  have hy_ok := (List.all_eq_true.mp hx_ok.2) y hy'
  rw [Bool.or_eq_true, Bool.or_eq_true] at hy_ok
  rcases hy_ok with (hge | heq1) | heq2
  · have hge' : rc.r ≤ y := by simpa [decide_eq_true_eq] using hge
    have hyr' : y < rc.r := hyr
    omega
  · left; exact beq_iff_eq.mp heq1
  · right; exact beq_iff_eq.mp heq2

private theorem mem_of_mem_dropLast {α : Type} {l : List α} {x : α}
    (h : x ∈ l.dropLast) : x ∈ l := by
  induction l with
  | nil => simp at h
  | cons a tl ih =>
    cases tl with
    | nil => simp at h
    | cons b tl' =>
      simp only [List.dropLast] at h
      rw [List.mem_cons] at h ⊢
      rcases h with rfl | htl
      · exact Or.inl rfl
      · exact Or.inr (ih htl)

private theorem face_cube_of_faceDegree_eq_three
    (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    (h_tri : ∀ d : T.Dart, d ∈ darts → faceDegree T d darts.length = 3)
    (x : T.Dart) :
    T.face.f (T.face.f (T.face.f x)) = x := by
  have h3 : (getOrbit T.face darts.length x).length = 3 := h_tri x (h_all x)
  have hper := _root_.Hypermap.perm_iter_length_getOrbit_eq_self_of_complete
    T.face darts h_all (Nat.le_refl darts.length) x
  rw [h3] at hper
  simpa [_root_.Hypermap.Perm.iter] using hper

private theorem perm_iter_mod_deg
    (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    {fuel : Nat} (h_len : darts.length ≤ fuel)
    (orient : Bool) (d : T.Dart) (hdeg_pos : 0 < nodeDegree T d fuel) (k : Nat) :
    _root_.Hypermap.Perm.iter (nodePermOriented T orient) k d =
      _root_.Hypermap.Perm.iter (nodePermOriented T orient) (k % nodeDegree T d fuel) d := by
  have hperiod := perm_iter_nodePermOriented_deg_eq_self T darts h_all h_len orient d
  have hmul : ∀ q r, r < nodeDegree T d fuel →
      _root_.Hypermap.Perm.iter (nodePermOriented T orient) (nodeDegree T d fuel * q + r) d =
        _root_.Hypermap.Perm.iter (nodePermOriented T orient) r d := by
    intro q
    induction q with
    | zero =>
      intro r _; simp
    | succ q ih =>
      intro r hr
      have harith : nodeDegree T d fuel * (q + 1) + r =
          (nodeDegree T d fuel * q + r) + nodeDegree T d fuel := by
        rw [Nat.mul_succ]; omega
      rw [harith, _root_.Hypermap.Perm.iter_add, hperiod]
      exact ih r hr
  have hdiv : k = nodeDegree T d fuel * (k / nodeDegree T d fuel) + k % nodeDegree T d fuel :=
    (Nat.div_add_mod k (nodeDegree T d fuel)).symm
  have hres := hmul (k / nodeDegree T d fuel) (k % nodeDegree T d fuel) (Nat.mod_lt k hdeg_pos)
  rwa [← hdiv] at hres

/-- A faithful triangulation embedding of configuration `c` into a triangulation hypermap `T`
    whose darts are enumerated by `darts`:
    - `rep : Nat → T.Dart` assigns a canonical dart in `T` to every vertex `i < c.totalNodes`;
    - `dart : Nat → Nat → T.Dart` assigns an explicit oriented edge dart `(u → v)` for every
      interior vertex `u ∈ [c.ringSize, c.totalNodes)` and neighbor `v < c.totalNodes`;
    - `orient : Bool` records whether cyclic adjacency around interior vertices matches `T.node`
      or `T.node.inv` (`nodePermOriented T orient`). -/
structure TriangulationEmbedding (c : Configuration) (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) where
  rep : Nat → T.Dart
  dart : Nat → Nat → T.Dart
  orient : Bool
  int_nonempty : ∀ u, c.ringSize ≤ u → u < c.totalNodes → ∃ v, v < c.totalNodes ∧ c.adj u v = true
  dart_same_vertex_rep : ∀ u, c.ringSize ≤ u → u < c.totalNodes →
    ∀ v, v < c.totalNodes → c.adj u v = true →
    sameVertex T (dart u v) (rep u) darts.length = true
  dart_edge_same_vertex_rep : ∀ u, c.ringSize ≤ u → u < c.totalNodes →
    ∀ v, v < c.totalNodes → c.adj u v = true →
    sameVertex T (T.edge.f (dart u v)) (rep v) darts.length = true
  adj_rep_edge : ∀ i j, i < c.totalNodes → j < c.totalNodes → c.adj i j = true →
    areAdjacentVertices T (rep i) (rep j) darts.length = true
  adj_rep_distinct : ∀ i j, i < c.totalNodes → j < c.totalNodes → c.adj i j = true →
    sameVertex T (rep i) (rep j) darts.length = false
  int_distinct : ∀ u1 u2,
    c.ringSize ≤ u1 → u1 < c.totalNodes →
    c.ringSize ≤ u2 → u2 < c.totalNodes →
    u1 ≠ u2 → sameVertex T (rep u1) (rep u2) darts.length = false
  int_ring_distinct : ∀ u x,
    c.ringSize ≤ u → u < c.totalNodes → x < c.ringSize →
    sameVertex T (rep u) (rep x) darts.length = false
  int_inj_neighbor : ∀ u, c.ringSize ≤ u → u < c.totalNodes →
    ∀ v1 v2, v1 < c.totalNodes → v2 < c.totalNodes →
    c.adj u v1 = true → c.adj u v2 = true →
    v1 ≠ v2 → dart u v1 ≠ dart u v2
  int_degree_match : ∀ u, c.ringSize ≤ u → u < c.totalNodes →
    nodeDegree T (rep u) darts.length = (List.range c.totalNodes).countP (fun w => c.adj u w)
  int_edge_flip : ∀ u v,
    c.ringSize ≤ u → u < c.totalNodes →
    c.ringSize ≤ v → v < c.totalNodes →
    c.adj u v = true → T.edge.f (dart u v) = dart v u

/-- Configuration `c` appears faithfully embedded in the triangulation `T`. -/
def AppearsInTriangulation (c : Configuration) (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) : Prop :=
  Nonempty (TriangulationEmbedding c T darts)

/-- Cyclic neighbor darts around every interior vertex `u` of `rc` step by `nodePermOriented T e.orient`. -/
def MatchesConfCycle (rc : FastReducer.RConf) (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (e : TriangulationEmbedding (configOfRConf rc) T darts) : Prop :=
  ∀ u, rc.r ≤ u → u < rc.n →
    ∀ hu : u < rc.adj.size,
      let nbrs := (rc.adj[u]'hu).toList
      ∀ (j : Nat) (hj : j < nbrs.length),
        e.dart u (nbrs[(j + 1) % nbrs.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hj))) =
          (nodePermOriented T e.orient).f (e.dart u (nbrs[j]'hj))

private theorem matchesConfCycleFn_of_mem_cyc {h : Nat} (hh : h < 633)
    {T : Hypermap} (dartFn : Nat → Nat → T.Dart) (orient : Bool)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    (hmc : ∀ u, (parsedRConfList[h]'hlen).r ≤ u → u < (parsedRConfList[h]'hlen).n →
      ∀ hu : u < (parsedRConfList[h]'hlen).adj.size,
        let nbrs := ((parsedRConfList[h]'hlen).adj[u]'hu).toList
        ∀ (j : Nat) (hj : j < nbrs.length),
          dartFn u (nbrs[(j + 1) % nbrs.length]'(Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hj))) =
            (nodePermOriented T orient).f (dartFn u (nbrs[j]'hj)))
    {iu : Nat} (hiu : iu < (configOfRConf (parsedRConfList[h]'hlen)).interiorSize)
    (hiu_fc : iu < (lookupFastConfRec h).intVerts.length := by
      have hh' := (fastConf_equiv_header h hh).2.2.2.2.2.2.2.2.2.2.1
      rw [hh']; exact hiu)
    {cp : CycPair} (hcp : cp ∈ ((lookupFastConfRec h).intVerts[iu]'hiu_fc).cyc) :
    dartFn ((configOfRConf (parsedRConfList[h]'hlen)).ringSize + iu) (cp.w - 1) =
      (nodePermOriented T orient).f
        (dartFn ((configOfRConf (parsedRConfList[h]'hlen)).ringSize + iu) (cp.v - 1)) := by
  have hhdr := fastConf_equiv_header h hh
  have hiv := fastConf_equiv_intVerts h hh iu hiu
  dsimp only at hhdr hiv
  let rc := parsedRConfList[h]'hlen
  let c := configOfRConf rc
  have hr_eq : c.ringSize = rc.r := hhdr.2.2.1
  have hn_eq : c.totalNodes = rc.n := hhdr.2.2.2.2.1
  have hint_eq : c.interiorSize = rc.n - rc.r := hhdr.2.2.2.1
  have hu_lt_n : c.ringSize + iu < rc.n := by
    have hc_4 : 4 ≤ rc.n - rc.r := by rw [← hint_eq]; exact hhdr.2.2.2.2.2.2.2.1
    have hsum : c.ringSize + iu < c.ringSize + c.interiorSize := Nat.add_lt_add_left hiu _
    rw [hr_eq, hint_eq] at hsum
    omega
  have hu_ge_r : rc.r ≤ c.ringSize + iu := by omega
  have hu_adj : c.ringSize + iu < rc.adj.size := by rw [hhdr.2.2.2.2.2.2.2.2.2.2.2.1, hn_eq]; exact hu_lt_n
  let nbrs := (rc.adj[c.ringSize + iu]'hu_adj).toList
  have hcyc_len : ((lookupFastConfRec h).intVerts[iu]'hiu_fc).cyc.length = nbrs.length :=
    hiv.2.2.2.2.2.2.2.1
  have hcyc_eq := hiv.2.2.2.2.2.2.2.2.1
  obtain ⟨j, hj_cyc, hcp_eq⟩ := List.mem_iff_getElem.mp hcp
  have hj_nbr : j < nbrs.length := by rw [← hcyc_len]; exact hj_cyc
  have heq := hcyc_eq j hj_nbr hj_cyc
  rw [hcp_eq] at heq
  have hmc_step := hmc (c.ringSize + iu) hu_ge_r hu_lt_n hu_adj j hj_nbr
  have hj1_pos : 0 < nbrs.length := Nat.lt_of_le_of_lt (Nat.zero_le j) hj_nbr
  by_cases hj1 : j + 1 < nbrs.length
  · have hmod : (j + 1) % nbrs.length = j + 1 := Nat.mod_eq_of_lt hj1
    have hv_eq : cp.v = nbrs[j] + 1 := by
      have hv := congrArg CycPair.v heq
      dsimp only at hv
      simpa [nbrs, rc, c] using hv
    have hw_eq : cp.w = nbrs[j + 1] + 1 := by
      have hw := congrArg CycPair.w heq
      dsimp only at hw
      have hj1' : j + 1 < (parsedRConfList[h]'hlen).adj[(configOfRConf (parsedRConfList[h]'hlen)).ringSize + iu].toList.length := by
        simpa [nbrs, rc, c] using hj1
      rw [dif_pos hj1'] at hw
      simpa [nbrs, rc, c] using hw
    have hmod' : (j + 1) % (parsedRConfList[h]'hlen).adj[(configOfRConf (parsedRConfList[h]'hlen)).ringSize + iu].size = j + 1 := by
      simpa [nbrs, rc, c] using hmod
    have hmc' : dartFn (c.ringSize + iu) (nbrs[j + 1]'hj1) =
        (nodePermOriented T orient).f (dartFn (c.ringSize + iu) (nbrs[j]'hj_nbr)) := by
      simpa [nbrs, rc, c, hmod'] using hmc_step
    simpa [c, rc, hv_eq, hw_eq] using hmc'
  · have hj_last : j + 1 = nbrs.length := by omega
    have hmod : (j + 1) % nbrs.length = 0 := by rw [hj_last, Nat.mod_self]
    have hv_eq : cp.v = nbrs[j] + 1 := by
      have hv := congrArg CycPair.v heq
      dsimp only at hv
      simpa [nbrs, rc, c] using hv
    have hw_eq : cp.w = nbrs[0] + 1 := by
      have hw := congrArg CycPair.w heq
      dsimp only at hw
      have hj1' : ¬ (j + 1 < (parsedRConfList[h]'hlen).adj[(configOfRConf (parsedRConfList[h]'hlen)).ringSize + iu].toList.length) := by
        simpa [nbrs, rc, c] using hj1
      rw [dif_neg hj1'] at hw
      simpa [nbrs, rc, c] using hw
    have hmod' : (j + 1) % (parsedRConfList[h]'hlen).adj[(configOfRConf (parsedRConfList[h]'hlen)).ringSize + iu].size = 0 := by
      simpa [nbrs, rc, c] using hmod
    have hmc' : dartFn (c.ringSize + iu) (nbrs[0]'hj1_pos) =
        (nodePermOriented T orient).f (dartFn (c.ringSize + iu) (nbrs[j]'hj_nbr)) := by
      simpa [nbrs, rc, c, hmod'] using hmc_step
    simpa [c, rc, hv_eq, hw_eq] using hmc'

theorem matchesConfCycle_of_mem_cyc {h : Nat} (hh : h < 633)
    {T : Hypermap} [DecidableEq T.Dart] {darts : List T.Dart}
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    {e : TriangulationEmbedding (configOfRConf (parsedRConfList[h]'hlen)) T darts}
    (hmc : MatchesConfCycle (parsedRConfList[h]'hlen) T darts e)
    {iu : Nat} (hiu : iu < (configOfRConf (parsedRConfList[h]'hlen)).interiorSize)
    (hiu_fc : iu < (lookupFastConfRec h).intVerts.length := by
      have hh' := (fastConf_equiv_header h hh).2.2.2.2.2.2.2.2.2.2.1
      rw [hh']; exact hiu)
    {cp : CycPair} (hcp : cp ∈ ((lookupFastConfRec h).intVerts[iu]'hiu_fc).cyc) :
    e.dart ((configOfRConf (parsedRConfList[h]'hlen)).ringSize + iu) (cp.w - 1) =
      (nodePermOriented T e.orient).f
        (e.dart ((configOfRConf (parsedRConfList[h]'hlen)).ringSize + iu) (cp.v - 1)) :=
  matchesConfCycleFn_of_mem_cyc hh e.dart e.orient hlen hmc hiu hiu_fc hcp

/-- Helper: extracting `(invMap, usedMask, cw, hinit, hspoke, hvert, hindu)` from `checkIsoRec = true`. -/
private theorem checkIsoRec_true_unpack {ring adjMat : Nat} {intVerts : List IntVert}
    {deg cur img : Nat}
    (hchk : checkIsoRec ring adjMat intVerts deg cur img = true) :
    ∃ invMap usedMask,
      initIsoVertsRec deg ring cur img intVerts = some (invMap, usedMask) ∧
      checkSpokeMaskRec deg usedMask = true ∧
      checkAllVertCycsRec deg ring cur img (!(getImgNat img 0).beq 0) intVerts = true ∧
      checkAllInduRec deg cur usedMask invMap adjMat = true := by
  dsimp [checkIsoRec] at hchk
  cases hinit : initIsoVertsRec deg ring cur img intVerts with
  | none => simp [hinit] at hchk
  | some p =>
    cases hspoke : checkSpokeMaskRec deg p.2 with
    | false => simp [hinit, hspoke] at hchk
    | true =>
      cases hvert : checkAllVertCycsRec deg ring cur img (!(getImgNat img 0).beq 0) intVerts with
      | false => simp [hinit, hspoke, hvert] at hchk
      | true =>
        simp [hinit, hspoke, hvert] at hchk
        exact ⟨p.1, p.2, rfl, hspoke, rfl, hchk⟩

private theorem intVert_of_ge_ring {h : Nat} (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    {u : Nat}
    (hur : (configOfRConf (parsedRConfList[h]'hlen)).ringSize ≤ u)
    (hun : u < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes) :
    ∃ (iu : Nat), iu < (configOfRConf (parsedRConfList[h]'hlen)).interiorSize ∧
      ∃ (hiu_fc : iu < (lookupFastConfRec h).intVerts.length),
      ((lookupFastConfRec h).intVerts[iu]'hiu_fc) ∈ (lookupFastConfRec h).intVerts ∧
      ((lookupFastConfRec h).intVerts[iu]'hiu_fc).u = u + 1 ∧
      (configOfRConf (parsedRConfList[h]'hlen)).ringSize + iu = u := by
  have hhdr := fastConf_equiv_header h hh
  dsimp only at hhdr
  have h_tot : (configOfRConf (parsedRConfList[h]'hlen)).totalNodes =
      (configOfRConf (parsedRConfList[h]'hlen)).ringSize +
        (configOfRConf (parsedRConfList[h]'hlen)).interiorSize := by omega
  have hiu : u - (configOfRConf (parsedRConfList[h]'hlen)).ringSize <
      (configOfRConf (parsedRConfList[h]'hlen)).interiorSize := by omega
  have hiu_fc : u - (configOfRConf (parsedRConfList[h]'hlen)).ringSize <
      (lookupFastConfRec h).intVerts.length := by rw [hhdr.2.2.2.2.2.2.2.2.2.2.1]; exact hiu
  have hiv := fastConf_equiv_intVerts h hh (u - (configOfRConf (parsedRConfList[h]'hlen)).ringSize) hiu
  dsimp only at hiv
  refine ⟨u - (configOfRConf (parsedRConfList[h]'hlen)).ringSize, hiu, hiu_fc,
    List.getElem_mem hiu_fc, ?_, by omega⟩
  have hu_eq : (configOfRConf (parsedRConfList[h]'hlen)).ringSize +
      (u - (configOfRConf (parsedRConfList[h]'hlen)).ringSize) = u := by omega
  simpa [hu_eq] using hiv.1

private theorem mem_rot_is_adj {h : Nat} (hh : h < 633)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    {u k m : Nat}
    (_hur : (configOfRConf (parsedRConfList[h]'hlen)).ringSize ≤ u)
    (hun : u < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes)
    (hu_adj : u < (parsedRConfList[h]'hlen).adj.size)
    (hm : m < (((parsedRConfList[h]'hlen).adj[u]'hu_adj).toList.drop k ++
        ((parsedRConfList[h]'hlen).adj[u]'hu_adj).toList.take k).length) :
    let v := (((parsedRConfList[h]'hlen).adj[u]'hu_adj).toList.drop k ++
        ((parsedRConfList[h]'hlen).adj[u]'hu_adj).toList.take k)[m]'hm
    v < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes ∧
    (configOfRConf (parsedRConfList[h]'hlen)).adj u v = true := by
  have hadj := fastConf_equiv_adj h hh
  dsimp only at hadj
  let rc := parsedRConfList[h]'hlen
  let c := configOfRConf rc
  let rot := (rc.adj[u]'hu_adj).toList.drop k ++ (rc.adj[u]'hu_adj).toList.take k
  have hmem_rot : rot[m]'hm ∈ rot := List.getElem_mem hm
  have hmem_nbrs : rot[m]'hm ∈ (rc.adj[u]'hu_adj).toList :=
    (rotateList_mem _ k (rot[m]'hm)).mp hmem_rot
  have hv_lt : rot[m]'hm < c.totalNodes := ((hadj.1 u hun).2 _ hmem_nbrs).1
  have hadj_uv : c.adj u (rot[m]'hm) = true := by
    rw [hadj.2.1 u hun _ hv_lt, List.contains_eq_mem]
    simpa [decide_eq_true_eq] using hmem_nbrs
  exact ⟨hv_lt, hadj_uv⟩

private theorem canonCartDart_rot_chain {h : Nat} (hh : h < 633)
    {T : Hypermap} [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    (h_tri : ∀ d : T.Dart, T.face.f (T.face.f (T.face.f d)) = d)
    (refl : Bool) (d0 : T.Dart)
    (hdeg5 : 5 ≤ nodeDegree T d0 darts.length)
    (hdeg11 : nodeDegree T d0 darts.length ≤ 11)
    (hmin5 : ∀ r, 1 ≤ r → r ≤ 5 * nodeDegree T d0 darts.length →
      5 ≤ cartDegOriented T darts.length (nodeDegree T d0 darts.length) refl d0 r)
    (hcw : CartwheelEmbedded T darts.length refl d0)
    {cur img usedMask : Nat} (cw : Bool)
    (hmask_iff : ∀ k, usedMask.testBit k = true ↔
      ∃ iv, iv ∈ (lookupFastConfRec h).intVerts ∧ getImgNat img iv.u = k)
    (hexact : ∀ iv, iv ∈ (lookupFastConfRec h).intVerts →
      getImgNat img iv.u ≤ 5 * nodeDegree T d0 darts.length ∧
      iv.d = getUppStrict (nodeDegree T d0 darts.length) cur (getImgNat img iv.u) ∧
      cartDegOriented T darts.length (nodeDegree T d0 darts.length) refl d0 (getImgNat img iv.u) = iv.d)
    (hvert : checkAllVertCycsRec (nodeDegree T d0 darts.length) (lookupFastConfRec h).ring cur img cw
      (lookupFastConfRec h).intVerts = true)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    {u k : Nat}
    (hur : (configOfRConf (parsedRConfList[h]'hlen)).ringSize ≤ u)
    (hun : u < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes)
    (hu_adj : u < (parsedRConfList[h]'hlen).adj.size)
    (hk : k < ((parsedRConfList[h]'hlen).adj[u]'hu_adj).toList.length)
    (a len : Nat) (halen : a + len ≤ (((parsedRConfList[h]'hlen).adj[u]'hu_adj).toList.drop k ++
        ((parsedRConfList[h]'hlen).adj[u]'hu_adj).toList.take k).length)
    (h_int : ∀ s (hs : s < len),
      (configOfRConf (parsedRConfList[h]'hlen)).ringSize ≤
        (((parsedRConfList[h]'hlen).adj[u]'hu_adj).toList.drop k ++
          ((parsedRConfList[h]'hlen).adj[u]'hu_adj).toList.take k)[a + s]'(by omega))
    (h2 : 2 ≤ len) :
    let rot := ((parsedRConfList[h]'hlen).adj[u]'hu_adj).toList.drop k ++
      ((parsedRConfList[h]'hlen).adj[u]'hu_adj).toList.take k
    let deg := nodeDegree T d0 darts.length
    let cd := cartDegOriented T darts.length deg refl d0
    let fu := getImgNat img (u + 1)
    let orient := if cw = true then refl else !refl
    let d_start := canonCartDart T deg refl d0 cd fu (getImgNat img (rot[a]'(by dsimp only [rot]; omega) + 1))
    ∀ s (hs : s < len),
      let w := rot[a + s]'(by dsimp only [rot]; omega)
      let fw := getImgNat img (w + 1)
      (∃ i, 1 ≤ i ∧ i ≤ deg ∧ (spokeEdgeDart T deg refl d0 i (cd i) fu fw).isSome = true) ∧
      canonCartDart T deg refl d0 cd fu fw =
        _root_.Hypermap.Perm.iter (nodePermOriented T orient) s d_start := by
  intro rot deg cd fu orient d_start
  let c := configOfRConf (parsedRConfList[h]'hlen)
  have hhdr := fastConf_equiv_header h hh
  dsimp only at hhdr
  obtain ⟨iu, hiu, hiu_fc, hivu_mem, hivu_u, hiu_eq⟩ := intVert_of_ge_ring hh hlen hur hun
  let ivu := (lookupFastConfRec h).intVerts[iu]'hiu_fc
  have hivu_eq : ivu.u = u + 1 := hivu_u
  have hiv := fastConf_equiv_intVerts h hh iu hiu
  dsimp only at hiv
  have hiu_adj : c.ringSize + iu = u := hiu_eq
  let nbrs := ((parsedRConfList[h]'hlen).adj[u]'hu_adj).toList
  have hrot_len : rot.length = nbrs.length := rotateList_length nbrs k
  have hcyc_len : ivu.cyc.length = nbrs.length := by
    simpa [c, ivu, hiu_adj, nbrs, Array.length_toList] using hiv.2.2.2.2.2.2.2.1
  have hcyc_eq := hiv.2.2.2.2.2.2.2.2.1
  have hstep : ∀ s (hs1 : s + 1 < len),
      let v1 := rot[a + s]'(by dsimp only [rot]; omega)
      let v2 := rot[a + (s + 1)]'(by dsimp only [rot]; omega)
      (∃ i1, 1 ≤ i1 ∧ i1 ≤ deg ∧
        (spokeEdgeDart T deg refl d0 i1 (cd i1) fu (getImgNat img (v1 + 1))).isSome = true) ∧
      (∃ i2, 1 ≤ i2 ∧ i2 ≤ deg ∧
        (spokeEdgeDart T deg refl d0 i2 (cd i2) fu (getImgNat img (v2 + 1))).isSome = true) ∧
      canonCartDart T deg refl d0 cd fu (getImgNat img (v2 + 1)) =
        (nodePermOriented T orient).f
          (canonCartDart T deg refl d0 cd fu (getImgNat img (v1 + 1))) := by
    intro s hs1
    have hm1 : a + s < rot.length := by dsimp only [rot]; omega
    have hm2 : a + (s + 1) < rot.length := by dsimp only [rot]; omega
    have hvr1 : c.ringSize ≤ rot[a + s]'hm1 := h_int s (by omega)
    have hvr2 : c.ringSize ≤ rot[a + (s + 1)]'hm2 := h_int (s + 1) (by omega)
    have hvn1 := (mem_rot_is_adj hh hlen hur hun hu_adj (k := k) (m := a + s) hm1).1
    have hvn2 := (mem_rot_is_adj hh hlen hur hun hu_adj (k := k) (m := a + (s + 1)) hm2).1
    obtain ⟨iv1_i, hiv1_i, hiv1_fc, hiv1_mem, hiv1_u, _⟩ := intVert_of_ge_ring hh hlen hvr1 hvn1
    obtain ⟨iv2_i, hiv2_i, hiv2_fc, hiv2_mem, hiv2_u, _⟩ := intVert_of_ge_ring hh hlen hvr2 hvn2
    let iv1 := (lookupFastConfRec h).intVerts[iv1_i]'hiv1_fc
    let iv2 := (lookupFastConfRec h).intVerts[iv2_i]'hiv2_fc
    have hj_lt : (k + (a + s)) % nbrs.length < nbrs.length :=
      Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le k) hk)
    let j := (k + (a + s)) % nbrs.length
    have hj_cyc : j < ivu.cyc.length := by rw [hcyc_len]; exact hj_lt
    have hv1_eq : rot[a + s]'hm1 = nbrs[j]'hj_lt := rotateList_getElem nbrs hk hm1
    have hj1_lt : (j + 1) % nbrs.length < nbrs.length :=
      Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le k) hk)
    have hj1_mod : (k + (a + (s + 1))) % nbrs.length = (j + 1) % nbrs.length := by
      have harith : k + (a + (s + 1)) = (k + (a + s)) + 1 := by omega
      rw [harith, Nat.add_mod]
      have h1 := Nat.add_mod j 1 nbrs.length
      rw [Nat.mod_eq_of_lt hj_lt] at h1
      exact h1.symm
    have hv2_eq : rot[a + (s + 1)]'hm2 = nbrs[(j + 1) % nbrs.length]'hj1_lt := by
      have hraw := rotateList_getElem nbrs hk hm2
      rw [hraw]
      congr 1
    have hcp_mem : (ivu.cyc[j]'hj_cyc) ∈ ivu.cyc := List.getElem_mem hj_cyc
    have hadj_row : ((parsedRConfList[h]'hlen).adj[(configOfRConf (parsedRConfList[h]'hlen)).ringSize + iu]'(
        by have h := hiu_adj; dsimp only [c] at h; rw [h]; exact hu_adj)).toList = nbrs := by
      simp [c, nbrs, hiu_adj]
    have hcyc_lt : j < ((parsedRConfList[h]'hlen).adj[(configOfRConf (parsedRConfList[h]'hlen)).ringSize + iu]'(
        by have h := hiu_adj; dsimp only [c] at h; rw [h]; exact hu_adj)).toList.length := by
      rw [hadj_row]; exact hj_lt
    have hcp_spec : ivu.cyc[j]'hj_cyc =
        { v := nbrs[j] + 1,
          w := if hj1 : j + 1 < nbrs.length then nbrs[j + 1] + 1 else nbrs[0] + 1 } := by
      simpa [ivu, hadj_row] using hcyc_eq j hcyc_lt hj_cyc
    have huv_eq : iv1.u = (ivu.cyc[j]'hj_cyc).v := by
      rw [hcp_spec, hiv1_u, hv1_eq]
    have huw_eq : iv2.u = (ivu.cyc[j]'hj_cyc).w := by
      rw [hcp_spec, hiv2_u, hv2_eq]
      by_cases hj1' : j + 1 < nbrs.length
      · simp [hj1', Nat.mod_eq_of_lt hj1']
      · have hj_last : j + 1 = nbrs.length := by omega
        simp [hj_last, Nat.mod_self]
    have hres := canonCartDart_step_of_cycPair hh darts h_all h_tri refl d0 hdeg5 hdeg11 hmin5 hcw
      cw hmask_iff hexact hvert hlen hivu_mem hiv1_mem hiv2_mem hcp_mem huv_eq huw_eq
    simpa [ivu, iv1, iv2, hivu_eq, hiv1_u, hiv2_u, deg, cd, fu, orient] using hres
  intro s hs
  induction s with
  | zero =>
    have hs1 : 0 + 1 < len := by omega
    refine ⟨(hstep 0 hs1).1, ?_⟩
    simp [d_start]
  | succ s ih =>
    have hs_prev : s < len := by omega
    have hs1 : s + 1 < len := by omega
    have hprev := ih hs_prev
    have hst := hstep s hs1
    refine ⟨hst.2.1, ?_⟩
    rw [hst.2.2, hprev.2]
    rfl

private theorem int_nbr_canonCartDart_eq {h : Nat} (hh : h < 633)
    {T : Hypermap} [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    (h_tri : ∀ d : T.Dart, T.face.f (T.face.f (T.face.f d)) = d)
    (refl : Bool) (d0 : T.Dart)
    (hdeg5 : 5 ≤ nodeDegree T d0 darts.length)
    (hdeg11 : nodeDegree T d0 darts.length ≤ 11)
    (hmin5 : ∀ r, 1 ≤ r → r ≤ 5 * nodeDegree T d0 darts.length →
      5 ≤ cartDegOriented T darts.length (nodeDegree T d0 darts.length) refl d0 r)
    (hcw : CartwheelEmbedded T darts.length refl d0)
    {cur img invMap usedMask : Nat} (cw : Bool)
    (hmask_iff : ∀ k, usedMask.testBit k = true ↔
      ∃ iv, iv ∈ (lookupFastConfRec h).intVerts ∧ getImgNat img iv.u = k)
    (himg_inj : ∀ iv1, iv1 ∈ (lookupFastConfRec h).intVerts →
      ∀ iv2, iv2 ∈ (lookupFastConfRec h).intVerts →
      iv1.u ≠ iv2.u → getImgNat img iv1.u ≠ getImgNat img iv2.u)
    (hinit : initIsoVertsRec (nodeDegree T d0 darts.length) (lookupFastConfRec h).ring cur img
      (lookupFastConfRec h).intVerts = some (invMap, usedMask))
    (hspoke : checkSpokeMaskRec (nodeDegree T d0 darts.length) usedMask = true)
    (hindu : checkAllInduRec (nodeDegree T d0 darts.length) cur usedMask invMap
      (lookupFastConfRec h).adjMat = true)
    (hm31 : MatchesCartState31 (nodeDegree T d0 darts.length)
      (cartDegOriented T darts.length (nodeDegree T d0 darts.length) refl d0) cur)
    (hexact : ∀ iv, iv ∈ (lookupFastConfRec h).intVerts →
      getImgNat img iv.u ≤ 5 * nodeDegree T d0 darts.length ∧
      iv.d = getUppStrict (nodeDegree T d0 darts.length) cur (getImgNat img iv.u) ∧
      cartDegOriented T darts.length (nodeDegree T d0 darts.length) refl d0 (getImgNat img iv.u) = iv.d)
    (hvert : checkAllVertCycsRec (nodeDegree T d0 darts.length) (lookupFastConfRec h).ring cur img cw
      (lookupFastConfRec h).intVerts = true)
    (hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh)
    {u k : Nat}
    (hur : (configOfRConf (parsedRConfList[h]'hlen)).ringSize ≤ u)
    (hun : u < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes)
    (hu_adj : u < (parsedRConfList[h]'hlen).adj.size)
    (hk : k < ((parsedRConfList[h]'hlen).adj[u]'hu_adj).toList.length)
    (hshape : IntRunShape (parsedRConfList[h]'hlen).r (configOfRConf (parsedRConfList[h]'hlen))
      (lookupFastConfRec h)
      ((lookupFastConfRec h).intVerts[u - (configOfRConf (parsedRConfList[h]'hlen)).ringSize]'(by
        have hhdr := fastConf_equiv_header h hh; dsimp only at hhdr
        rw [hhdr.2.2.2.2.2.2.2.2.2.2.1]; omega))
      (((parsedRConfList[h]'hlen).adj[u]'hu_adj).toList.drop k ++
        ((parsedRConfList[h]'hlen).adj[u]'hu_adj).toList.take k)) :
    let c := configOfRConf (parsedRConfList[h]'hlen)
    let rot := (parsedRConfList[h]'hlen).adj[u].toList.drop k ++
      (parsedRConfList[h]'hlen).adj[u].toList.take k
    let deg := nodeDegree T d0 darts.length
    let cd := cartDegOriented T darts.length deg refl d0
    let fu := getImgNat img (u + 1)
    let orient := if cw = true then refl else !refl
    have h0_pos : 0 < rot.length := by
      dsimp only [rot]
      rw [rotateList_length _ k]
      omega
    let baseDart := canonCartDart T deg refl d0 cd fu (getImgNat img (rot[0]'h0_pos + 1))
    sameVertex T baseDart (cartDartOriented T deg refl d0 fu) darts.length = true ∧
    nodeDegree T baseDart darts.length = rot.length ∧
    ∀ m (hm : m < rot.length), c.ringSize ≤ rot[m]'hm →
      (∃ i, 1 ≤ i ∧ i ≤ deg ∧
        (spokeEdgeDart T deg refl d0 i (cd i) fu (getImgNat img (rot[m]'hm + 1))).isSome = true) ∧
      canonCartDart T deg refl d0 cd fu (getImgNat img (rot[m]'hm + 1)) =
        _root_.Hypermap.Perm.iter (nodePermOriented T orient) m baseDart := by
  intro c rot deg cd fu orient h0_pos baseDart
  have hhdr := fastConf_equiv_header h hh
  have hadj := fastConf_equiv_adj h hh
  dsimp only at hhdr hadj
  have hr_eq : c.ringSize = (parsedRConfList[h]'hlen).r := hhdr.2.2.1
  have h_len := Nat.le_refl darts.length
  obtain ⟨iu, hiu, hiu_fc, hivu_mem, hivu_u, hiu_eq⟩ := intVert_of_ge_ring hh hlen hur hun
  have hiv := fastConf_equiv_intVerts h hh iu hiu
  dsimp only at hiv
  have hiu_adj : c.ringSize + iu = u := hiu_eq
  have hid_eq : ((lookupFastConfRec h).intVerts[iu]'hiu_fc).d =
      (parsedRConfList[h]'hlen).adj[u].toList.length := by
    simpa [c, hiu_adj, Array.length_toList] using hiv.2.1
  have hrot_len : rot.length = (parsedRConfList[h]'hlen).adj[u].toList.length :=
    rotateList_length _ k
  have hrot_nd : rot.Nodup := rotateList_nodup (hadj.1 u hun).1 k
  have hdeg_fu : cd fu = rot.length := by
    have hex_u := (hexact _ hivu_mem).2.2
    rw [hivu_u] at hex_u
    change cd fu = _ at hex_u
    rw [hex_u, hid_eq, ← hrot_len]
  have hchain_prefix : ∀ {a len : Nat} (halen : a + len ≤ rot.length)
      (hint_sub : ∀ s (hs : s < len), c.ringSize ≤ rot[a + s]'(by omega))
      (hlen2 : 2 ≤ len),
      sameVertex T (canonCartDart T deg refl d0 cd fu (getImgNat img (rot[a]'(by omega) + 1)))
        (cartDartOriented T deg refl d0 fu) darts.length = true ∧
      ∀ s (hs : s < len),
        (∃ i, 1 ≤ i ∧ i ≤ deg ∧
          (spokeEdgeDart T deg refl d0 i (cd i) fu (getImgNat img (rot[a + s]'(by omega) + 1))).isSome = true) ∧
        canonCartDart T deg refl d0 cd fu (getImgNat img (rot[a + s]'(by omega) + 1)) =
          _root_.Hypermap.Perm.iter (nodePermOriented T orient) s
            (canonCartDart T deg refl d0 cd fu (getImgNat img (rot[a]'(by omega) + 1))) := by
    intro a len halen hint_sub hlen2
    have hch := canonCartDart_rot_chain hh darts h_all h_tri refl d0 hdeg5 hdeg11 hmin5 hcw
      cw hmask_iff hexact hvert hlen hur hun hu_adj hk a len halen hint_sub hlen2
    dsimp only at hch
    obtain ⟨⟨i0, hi01, hi0_deg, hs0⟩, _⟩ := hch 0 (by omega)
    rw [Option.isSome_iff_exists] at hs0
    obtain ⟨d_sp, hd_sp⟩ := hs0
    have hspec := spokeEdgeDart_spec T darts h_all h_len h_tri refl d0 hdeg5 hi01 hi0_deg hd_sp
    have heq_sp := spokeEdgeDart_eq_canonCartDart T darts h_all h_len h_tri refl d0 hdeg5
      hcw hi01 hi0_deg hd_sp
    have hsame : sameVertex T
        (canonCartDart T deg refl d0 cd fu (getImgNat img (rot[a]'(by omega) + 1)))
        (cartDartOriented T deg refl d0 fu) darts.length = true := by
      simpa [← heq_sp] using hspec.2.2.2.2.2.1
    exact ⟨hsame, hch⟩
  have hbase_facts : ∀ (len2 : Nat) (hlen2 : 2 ≤ len2) (hlen2_le : len2 ≤ rot.length),
      (∀ s (hs : s < len2), c.ringSize ≤ rot[s]'(Nat.lt_of_lt_of_le hs hlen2_le)) →
      sameVertex T baseDart (cartDartOriented T deg refl d0 fu) darts.length = true ∧
      nodeDegree T baseDart darts.length = rot.length := by
    intro len2 hlen2 hlen2_le hint_sub
    have hp := hchain_prefix (a := 0) (len := len2) (by simpa using hlen2_le)
      (fun s hs => by
        have hidx : rot[0 + s]'(by omega) = rot[s]'(Nat.lt_of_lt_of_le hs hlen2_le) := by
          congr 1; omega
        rw [hidx]; exact hint_sub s hs) hlen2
    have hsame : sameVertex T baseDart (cartDartOriented T deg refl d0 fu) darts.length = true := by
      simpa [baseDart] using hp.1
    have hdeg_b : nodeDegree T baseDart darts.length = rot.length := by
      rw [← nodeDegree_eq_of_sameVertex T darts h_all h_len hsame]
      exact hdeg_fu
    exact ⟨hsame, hdeg_b⟩
  cases hshape with
  | allInterior h_all_int h5 =>
    have h5_rot : 5 ≤ rot.length := h5
    obtain ⟨hsame_b, hdeg_b⟩ := hbase_facts rot.length (by omega) (Nat.le_refl _) (fun s hs => by
      have := h_all_int _ (List.getElem_mem hs); omega)
    have hp := hchain_prefix (a := 0) (len := rot.length) (by omega)
      (fun s hs => by
        have hidx : rot[0 + s]'(by omega) = rot[s]'hs := by congr 1; omega
        rw [hidx]; have := h_all_int _ (List.getElem_mem hs); omega) (by omega)
    refine ⟨hsame_b, hdeg_b, fun m hm _ => ?_⟩
    have hms := hp.2 m hm
    have hidx : rot[0 + m]'(by omega) = rot[m]'hm := by congr 1; omega
    simpa [baseDart, hidx] using hms
  | @oneRingRun p1 g1 hrot_eq hp1_len hg1_len hp1_int hg1_ring =>
    have hp1_le : p1.length ≤ rot.length := by dsimp only [rot]; rw [hrot_eq, List.length_append]; omega
    have hp1_sub : ∀ s (hs : s < p1.length), c.ringSize ≤ rot[s]'(Nat.lt_of_lt_of_le hs hp1_le) := by
      intro s hs
      have hget : rot[s]'(Nat.lt_of_lt_of_le hs hp1_le) = p1[s]'hs := by
        rw [List.getElem_of_eq hrot_eq (Nat.lt_of_lt_of_le hs hp1_le), List.getElem_append_left hs]
      rw [hget]
      have := hp1_int _ (List.getElem_mem hs)
      omega
    obtain ⟨hsame_b, hdeg_b⟩ := hbase_facts p1.length hp1_len hp1_le hp1_sub
    have hp := hchain_prefix (a := 0) (len := p1.length) (by simpa using hp1_le)
      (fun s hs => by
        have hidx : rot[0 + s]'(by omega) = rot[s]'(Nat.lt_of_lt_of_le hs hp1_le) := by
          congr 1; omega
        rw [hidx]; exact hp1_sub s hs) hp1_len
    refine ⟨hsame_b, hdeg_b, fun m hm hrm => ?_⟩
    have hm_lt : m < p1.length := by
      exact Classical.byContradiction fun hge => by
        have hge' : p1.length ≤ m := by omega
        have hmem_g1 : rot[m]'hm ∈ g1 := by
          have hm' : m - p1.length < g1.length := by
            have : rot.length = p1.length + g1.length := by
              dsimp only [rot]; rw [hrot_eq, List.length_append]
            omega
          have happ : rot[m]'hm = (p1 ++ g1)[m]'(by rw [← hrot_eq]; exact hm) :=
            List.getElem_of_eq hrot_eq hm
          have : rot[m]'hm = g1[m - p1.length]'hm' := by
            rw [happ, List.getElem_append_right hge']
          rw [this]; exact List.getElem_mem hm'
        have := hg1_ring _ hmem_g1
        omega
    have hms := hp.2 m hm_lt
    have hidx : rot[0 + m]'(by omega) = rot[m]'hm := by congr 1; omega
    simpa [baseDart, hidx] using hms
  | @twoRingGaps p1 p2 x1 x2 hrot_eq hp1_len hp2_len hx1 hx2 _ _ hp1_int hp2_int
      h_adj_ends _ =>
    let m1 := p1.length
    let m2 := p2.length
    have hrot_total : rot.length = m1 + m2 + 2 := by
      dsimp only [rot]
      rw [hrot_eq]
      simp only [List.length_append, List.length_cons, List.length_nil]
      dsimp only [m1, m2]
      omega
    have hm1_sub : ∀ s (hs : s < m1), c.ringSize ≤ rot[s]'(by dsimp only [m1, m2] at hrot_total ⊢; omega) := by
      intro s hs
      have hget : rot[s]'(by dsimp only [m1, m2] at hrot_total ⊢; omega) = p1[s]'hs := by
        have happ : rot = p1 ++ ([x1] ++ p2 ++ [x2]) := by simpa [List.append_assoc] using hrot_eq
        rw [List.getElem_of_eq happ (by dsimp only [m1, m2] at hrot_total ⊢; omega),
          List.getElem_append_left hs]
      rw [hget]; have := hp1_int _ (List.getElem_mem hs); omega
    obtain ⟨hsame_b, hdeg_b⟩ := hbase_facts m1 hp1_len (by dsimp only [m1, m2] at hrot_total; omega) hm1_sub
    have hp1 := hchain_prefix (a := 0) (len := m1) (by dsimp only [m1, m2] at hrot_total; omega)
      (fun s hs => by
        have hidx : rot[0 + s]'(by dsimp only [m1, m2] at hrot_total ⊢; omega) =
            rot[s]'(by dsimp only [m1, m2] at hrot_total ⊢; omega) := by congr 1; omega
        rw [hidx]; exact hm1_sub s hs) hp1_len
    have hm2_sub : ∀ s (hs : s < m2),
        c.ringSize ≤ rot[(m1 + 1) + s]'(by dsimp only [m1, m2] at hrot_total ⊢; omega) := by
      intro s hs
      have hget : rot[(m1 + 1) + s]'(by dsimp only [m1, m2] at hrot_total ⊢; omega) = p2[s]'hs := by
        have happ : rot = ((p1 ++ [x1]) ++ p2) ++ [x2] := by simpa [List.append_assoc] using hrot_eq
        have hge : (p1 ++ [x1]).length ≤ (m1 + 1) + s := by
          dsimp only [m1]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
        have hlt' : (m1 + 1) + s < ((p1 ++ [x1]) ++ p2).length := by
          dsimp only [m1, m2] at *; simp only [List.length_append, List.length_cons, List.length_nil]; omega
        rw [List.getElem_of_eq happ (by dsimp only [m1, m2] at hrot_total ⊢; omega),
          List.getElem_append_left hlt', List.getElem_append_right hge]
        congr 1
        dsimp only [m1]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [hget]; have := hp2_int _ (List.getElem_mem hs); omega
    have hp2 := hchain_prefix (a := m1 + 1) (len := m2)
      (by dsimp only [m1, m2] at hrot_total; omega) hm2_sub hp2_len
    let d_a2 := canonCartDart T deg refl d0 cd fu
      (getImgNat img (rot[m1 + 1]'(by dsimp only [m1, m2] at hrot_total; omega) + 1))
    have hsame_a2_base : sameVertex T d_a2 baseDart darts.length = true := by
      have h1 : sameVertex T d_a2 (cartDartOriented T deg refl d0 fu) darts.length = true := hp2.1
      have h2 := hsame_b
      rw [sameVertex_symm_of_complete T darts h_all h_len] at h2
      exact sameVertex_trans_of_complete T darts h_all h_len h1 h2
    have ha2_orb : d_a2 ∈ getOrbit T.node darts.length baseDart :=
      (sameVertex_iff_mem_getOrbit T darts h_all h_len baseDart d_a2).mp hsame_a2_base
    obtain ⟨t, ht_deg, ht_eq⟩ :=
      (mem_getOrbit_nodePermOriented_iff T darts h_all h_len orient baseDart d_a2).mp ha2_orb
    dsimp only [d_a2] at ht_eq
    have ht_lt_n : t < rot.length := by rw [← hdeg_b]; exact ht_deg
    have h_no_hit : ∀ i (hi : i < m1) s (hs : s < m2), (t + s) % rot.length ≠ i := by
      intro i hi s hs heq_mod
      have hd_s := (hp2.2 s hs).2
      rw [Nat.add_comm t s] at heq_mod
      rw [ht_eq, ← _root_.Hypermap.Perm.iter_add,
        perm_iter_mod_deg T darts h_all h_len orient baseDart (by rw [hdeg_b]; omega),
        hdeg_b, heq_mod] at hd_s
      have hd_i := (hp1.2 i hi).2
      have hidx_i : rot[0 + i]'(by dsimp only [m1, m2] at hrot_total ⊢; omega) =
          rot[i]'(by dsimp only [m1, m2] at hrot_total ⊢; omega) := by congr 1; omega
      rw [hidx_i] at hd_i
      have hsame_d : canonCartDart T deg refl d0 cd fu
            (getImgNat img (rot[m1 + 1 + s]'(by dsimp only [m1, m2] at hrot_total ⊢; omega) + 1)) =
          canonCartDart T deg refl d0 cd fu
            (getImgNat img (rot[i]'(by dsimp only [m1, m2] at hrot_total ⊢; omega) + 1)) := by
        simpa [baseDart] using hd_s.trans hd_i.symm
      have hvr_s : c.ringSize ≤ rot[m1 + 1 + s]'(by dsimp only [m1, m2] at hrot_total ⊢; omega) := hm2_sub s hs
      have hvn_s := (mem_rot_is_adj hh hlen hur hun hu_adj (k := k) (m := m1 + 1 + s)
        (by dsimp only [m1, m2, rot] at hrot_total ⊢; omega)).1
      have hvr_i : c.ringSize ≤ rot[i]'(by dsimp only [m1, m2] at hrot_total ⊢; omega) := hm1_sub i hi
      have hvn_i := (mem_rot_is_adj hh hlen hur hun hu_adj (k := k) (m := i)
        (by dsimp only [m1, m2, rot] at hrot_total ⊢; omega)).1
      obtain ⟨ivs_i, hivs_i, hivs_fc, hivs_mem, hivs_u, _⟩ := intVert_of_ge_ring hh hlen hvr_s hvn_s
      obtain ⟨ivi_i, hivi_i, hivi_fc, hivi_mem, hivi_u, _⟩ := intVert_of_ge_ring hh hlen hvr_i hvn_i
      obtain ⟨isp_s, hisp_s1, hisp_sdeg, hs_some⟩ := (hp2.2 s hs).1
      obtain ⟨isp_i, hisp_i1, hisp_ideg, hi_some⟩ := (hp1.2 i hi).1
      have hsp_s := canonCartDart_edge_of_spokeSome T darts h_all h_len h_tri refl d0 hdeg5 hcw
        hisp_s1 hisp_sdeg hs_some
      have hsp_i := canonCartDart_edge_of_spokeSome T darts h_all h_len h_tri refl d0 hdeg5 hcw
        hisp_i1 hisp_ideg hi_some
      have hedge_eq := congrArg T.edge.f hsame_d
      have hsame_vs : sameVertex T
          (T.edge.f (canonCartDart T deg refl d0 cd fu
            (getImgNat img (rot[m1 + 1 + s]'(by dsimp only [m1, m2] at hrot_total ⊢; omega) + 1))))
          (cartDartOriented T deg refl d0
            (getImgNat img (rot[m1 + 1 + s]'(by dsimp only [m1, m2] at hrot_total ⊢; omega) + 1)))
          darts.length = true := hsp_s.2.2.2.2.2.2.1
      have hsame_vi : sameVertex T
          (T.edge.f (canonCartDart T deg refl d0 cd fu
            (getImgNat img (rot[i]'(by dsimp only [m1, m2] at hrot_total ⊢; omega) + 1))))
          (cartDartOriented T deg refl d0
            (getImgNat img (rot[i]'(by dsimp only [m1, m2] at hrot_total ⊢; omega) + 1)))
          darts.length = true := by simpa [hidx_i] using hsp_i.2.2.2.2.2.2.1
      rw [hedge_eq] at hsame_vs
      have hsame_vi' := hsame_vi
      rw [sameVertex_symm_of_complete T darts h_all h_len] at hsame_vi'
      have hcoll := sameVertex_trans_of_complete T darts h_all h_len hsame_vi' hsame_vs
      have hne_idx : m1 + 1 + s ≠ i := by omega
      have hne_val : rot[m1 + 1 + s]'(by dsimp only [m1, m2] at hrot_total ⊢; omega) ≠
          rot[i]'(by dsimp only [m1, m2] at hrot_total ⊢; omega) :=
        fun heq_v => hne_idx (nodup_getElem_inj hrot_nd (by dsimp only [m1, m2] at hrot_total ⊢; omega)
          (by dsimp only [m1, m2] at hrot_total ⊢; omega) heq_v)
      have hne_iu : ((lookupFastConfRec h).intVerts[ivs_i]'hivs_fc).u ≠
          ((lookupFastConfRec h).intVerts[ivi_i]'hivi_fc).u := by
        rw [hivs_u, hivi_u]; omega
      have hne_img := himg_inj _ hivs_mem _ hivi_mem hne_iu
      rw [hivs_u, hivi_u] at hne_img
      have hdisj := hcw.1 _ _
        (by simpa [hidx_i] using hsp_i.2.2.2.2.1) hsp_s.2.2.2.2.1 hne_img.symm
      exact Bool.false_ne_true (hdisj.symm.trans hcoll)
    have ht_ge : m1 ≤ t := by
      have h0 := h_no_hit
      exact Classical.byContradiction fun hlt => by
        have ht_lt : t < m1 := by omega
        exact h0 t ht_lt 0 (by omega)
          (by rw [Nat.add_zero]; exact Nat.mod_eq_of_lt (by dsimp only [m1, m2] at hrot_total; omega))
    have ht_le : t ≤ m1 + 2 := by
      exact Classical.byContradiction fun hgt => by
        have ht_ge3 : m1 + 3 ≤ t := by omega
        have hs_lt : rot.length - t < m2 := by dsimp only [m1, m2] at hrot_total; omega
        have h0 := h_no_hit 0 (by omega) (rot.length - t) hs_lt
        have hsum : t + (rot.length - t) = rot.length := by omega
        rw [hsum, Nat.mod_self] at h0
        exact h0 rfl
    obtain ⟨a1, b1, a2, b2, ha1, hb1, ha2, hb2, h_nb1a2, h_nb2a1⟩ := h_adj_ends
    have hb1_eq : rot[m1 - 1]'(by dsimp only [m1, m2] at hrot_total; omega) = b1 := by
      have hget : rot[m1 - 1]'(by dsimp only [m1, m2] at hrot_total; omega) = p1[m1 - 1]'(by omega) := by
        have happ : rot = p1 ++ ([x1] ++ p2 ++ [x2]) := by simpa [List.append_assoc] using hrot_eq
        rw [List.getElem_of_eq happ (by dsimp only [m1, m2] at hrot_total ⊢; omega),
          List.getElem_append_left (show m1 - 1 < p1.length by dsimp only [m1] at *; omega)]
      rw [hget]
      have hgl := List.getLast?_eq_some_getLast (show p1 ≠ [] by intro hnil; simp [hnil] at hp1_len)
      rw [hb1] at hgl
      have heq_b1 := Option.some.inj hgl
      rw [List.getLast_eq_getElem] at heq_b1
      dsimp only [m1] at *
      exact heq_b1.symm
    have ha2_eq : rot[m1 + 1]'(by dsimp only [m1, m2] at hrot_total; omega) = a2 := by
      have hget : rot[m1 + 1]'(by dsimp only [m1, m2] at hrot_total; omega) = p2[0]'(by omega) := by
        have happ : rot = ((p1 ++ [x1]) ++ p2) ++ [x2] := by simpa [List.append_assoc] using hrot_eq
        have hge : (p1 ++ [x1]).length ≤ m1 + 1 := by
          dsimp only [m1]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
        have hlt' : m1 + 1 < ((p1 ++ [x1]) ++ p2).length := by
          dsimp only [m1, m2] at *; simp only [List.length_append, List.length_cons, List.length_nil]; omega
        rw [List.getElem_of_eq happ (by dsimp only [m1, m2] at hrot_total ⊢; omega),
          List.getElem_append_left hlt', List.getElem_append_right hge]
        congr 1
        dsimp only [m1]
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [hget]
      have hhd := List.head?_eq_some_head (show p2 ≠ [] by intro hnil; simp [hnil] at hp2_len)
      rw [ha2] at hhd
      have heq_a2 := Option.some.inj hhd
      rw [List.head_eq_getElem] at heq_a2
      exact heq_a2.symm
    have ha1_eq : rot[0]'h0_pos = a1 := by
      have hget : rot[0]'h0_pos = p1[0]'(by omega) := by
        have happ : rot = p1 ++ ([x1] ++ p2 ++ [x2]) := by simpa [List.append_assoc] using hrot_eq
        rw [List.getElem_of_eq happ h0_pos, List.getElem_append_left (show 0 < p1.length by omega)]
      rw [hget]
      have hhd := List.head?_eq_some_head (show p1 ≠ [] by intro hnil; simp [hnil] at hp1_len)
      rw [ha1] at hhd
      have heq_a1 := Option.some.inj hhd
      rw [List.head_eq_getElem] at heq_a1
      exact heq_a1.symm
    have hb2_eq : rot[m1 + m2]'(by dsimp only [m1, m2] at hrot_total; omega) = b2 := by
      have hget : rot[m1 + m2]'(by dsimp only [m1, m2] at hrot_total; omega) = p2[m2 - 1]'(by omega) := by
        have happ : rot = ((p1 ++ [x1]) ++ p2) ++ [x2] := by simpa [List.append_assoc] using hrot_eq
        have hge : (p1 ++ [x1]).length ≤ m1 + m2 := by
          dsimp only [m1, m2] at *; simp only [List.length_append, List.length_cons, List.length_nil]; omega
        have hlt' : m1 + m2 < ((p1 ++ [x1]) ++ p2).length := by
          dsimp only [m1, m2] at *; simp only [List.length_append, List.length_cons, List.length_nil]; omega
        rw [List.getElem_of_eq happ (by dsimp only [m1, m2] at hrot_total ⊢; omega),
          List.getElem_append_left hlt', List.getElem_append_right hge]
        congr 1
        dsimp only [m1, m2] at *
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [hget]
      have hgl := List.getLast?_eq_some_getLast (show p2 ≠ [] by intro hnil; simp [hnil] at hp2_len)
      rw [hb2] at hgl
      have heq_b2 := Option.some.inj hgl
      rw [List.getLast_eq_getElem] at heq_b2
      dsimp only [m2] at *
      exact heq_b2.symm
    have hadj_of_turn : ∀ {x y : Nat}
        (hxr : c.ringSize ≤ x) (hxn : x < c.totalNodes)
        (hyr : c.ringSize ≤ y) (hyn : y < c.totalNodes)
        (hne_xy : x ≠ y)
        (hx_sp : ∃ i, 1 ≤ i ∧ i ≤ deg ∧
          (spokeEdgeDart T deg refl d0 i (cd i) fu (getImgNat img (x + 1))).isSome = true)
        (hy_sp : ∃ i, 1 ≤ i ∧ i ≤ deg ∧
          (spokeEdgeDart T deg refl d0 i (cd i) fu (getImgNat img (y + 1))).isSome = true)
        (hturn : canonCartDart T deg refl d0 cd fu (getImgNat img (y + 1)) =
          (nodePermOriented T orient).f
            (canonCartDart T deg refl d0 cd fu (getImgNat img (x + 1)))),
        c.adj x y = true := by
      intro x y hxr hxn hyr hyn hne_xy ⟨ix, hix1, hixd, hx_sp⟩ ⟨iy, hiy1, hiyd, hy_sp⟩ hturn
      have hsp_x := canonCartDart_edge_of_spokeSome T darts h_all h_len h_tri refl d0 hdeg5 hcw
        hix1 hixd hx_sp
      have hsp_y := canonCartDart_edge_of_spokeSome T darts h_all h_len h_tri refl d0 hdeg5 hcw
        hiy1 hiyd hy_sp
      have hadj_e := areAdjacentVertices_of_tri_fan_turn darts h_all h_len h_tri orient hturn
      have hsame_vx := hsp_x.2.2.2.2.2.2.1
      have hsame_vy := hsp_y.2.2.2.2.2.2.1
      have hadj_cart : areAdjacentVertices T
          (cartDartOriented T deg refl d0 (getImgNat img (x + 1)))
          (cartDartOriented T deg refl d0 (getImgNat img (y + 1))) darts.length = true := by
        rw [← areAdjacentVertices_congr T darts h_all h_len hsame_vx hsame_vy]
        exact hadj_e
      obtain ⟨ivx_i, _, hivx_fc, hivx_mem, hivx_u, hivx_sum⟩ := intVert_of_ge_ring hh hlen hxr hxn
      obtain ⟨ivy_i, _, hivy_fc, hivy_mem, hivy_u, hivy_sum⟩ := intVert_of_ge_ring hh hlen hyr hyn
      have hne_ivu : ((lookupFastConfRec h).intVerts[ivx_i]'hivx_fc).u ≠
          ((lookupFastConfRec h).intVerts[ivy_i]'hivy_fc).u := by
        rw [hivx_u, hivy_u]; omega
      have hne_f := himg_inj _ hivx_mem _ hivy_mem hne_ivu
      rw [hivx_u, hivy_u] at hne_f
      have hpca := hcw.2.1 _ _ hsp_x.2.2.2.2.1 hsp_y.2.2.2.2.1 hne_f hadj_cart
      have hx_bit : usedMask.testBit (getImgNat img (x + 1)) = true := by
        rw [hmask_iff]; exact ⟨_, hivx_mem, by rw [hivx_u]⟩
      have hy_bit : usedMask.testBit (getImgNat img (y + 1)) = true := by
        rw [hmask_iff]; exact ⟨_, hivy_mem, by rw [hivy_u]⟩
      have hpc := pureCartAdj_implies_c_adj hh hdeg5 hdeg11 hmin5 hm31 hlen hinit hspoke hindu
        hexact hx_bit hy_bit hpca
      dsimp only at hpc
      have h_all_spec := (initIsoVertsRec_sound hh hdeg11 hlen hinit).2.2.1
      have hln_x := (h_all_spec _ hivx_mem).2.2.2
      have hln_y := (h_all_spec _ hivy_mem).2.2.2
      rw [hivx_u] at hln_x; rw [hivy_u] at hln_y
      have hx_u0 : c.ringSize + getLaneNat invMap (getImgNat img (x + 1)) = x := by
        rw [hln_x]; omega
      have hy_v0 : c.ringSize + getLaneNat invMap (getImgNat img (y + 1)) = y := by
        rw [hln_y]; omega
      rw [hx_u0, hy_v0] at hpc
      exact hpc.1
    have ht_eq_m1_add_1 : t = m1 + 1 := by
      rcases (show t = m1 ∨ t = m1 + 1 ∨ t = m1 + 2 by omega) with ht | ht | ht
      · subst ht
        have hd_b1 := (hp1.2 (m1 - 1) (by omega)).2
        have hidx_b1 : rot[0 + (m1 - 1)]'(by dsimp only [m1, m2] at hrot_total; omega) =
            rot[m1 - 1]'(by dsimp only [m1, m2] at hrot_total; omega) := by congr 1; omega
        rw [hidx_b1] at hd_b1
        have hs_eq : _root_.Hypermap.Perm.iter (nodePermOriented T orient) m1 baseDart =
            (nodePermOriented T orient).f
              (_root_.Hypermap.Perm.iter (nodePermOriented T orient) (m1 - 1) baseDart) := by
          rw [show m1 = (m1 - 1) + 1 by omega]; rfl
        have hturn : canonCartDart T deg refl d0 cd fu
              (getImgNat img (rot[m1 + 1]'(by dsimp only [m1, m2] at hrot_total; omega) + 1)) =
            (nodePermOriented T orient).f
              (canonCartDart T deg refl d0 cd fu
                (getImgNat img (rot[m1 - 1]'(by dsimp only [m1, m2] at hrot_total; omega) + 1))) := by
          rw [ht_eq, hs_eq, ← hd_b1]
        have hb1_r : c.ringSize ≤ b1 := by rw [← hb1_eq]; exact hm1_sub (m1 - 1) (by omega)
        have hb1_n : b1 < c.totalNodes := by
          rw [← hb1_eq]
          exact (mem_rot_is_adj hh hlen hur hun hu_adj (k := k) (m := m1 - 1)
            (by dsimp only [m1, m2, rot] at hrot_total ⊢; omega)).1
        have ha2_r : c.ringSize ≤ a2 := by rw [← ha2_eq]; exact hm2_sub 0 (by omega)
        have ha2_n : a2 < c.totalNodes := by
          rw [← ha2_eq]
          exact (mem_rot_is_adj hh hlen hur hun hu_adj (k := k) (m := m1 + 1)
            (by dsimp only [m1, m2, rot] at hrot_total ⊢; omega)).1
        have hne_ba : b1 ≠ a2 := by
          rw [← hb1_eq, ← ha2_eq]
          intro heq
          have : m1 - 1 = m1 + 1 := nodup_getElem_inj hrot_nd
            (by dsimp only [m1, m2] at hrot_total; omega)
            (by dsimp only [m1, m2] at hrot_total; omega) heq
          omega
        have hsp_b1 := (hp1.2 (m1 - 1) (by omega)).1
        rw [hidx_b1] at hsp_b1
        have hidx_a2 : rot[(m1 + 1) + 0]'(by dsimp only [m1, m2] at hrot_total; omega) =
            rot[m1 + 1]'(by dsimp only [m1, m2] at hrot_total; omega) := rfl
        have hsp_a2 := (hp2.2 0 (by omega)).1
        rw [hidx_a2] at hsp_a2
        have hadj_ba := hadj_of_turn hb1_r hb1_n ha2_r ha2_n hne_ba
          (by rw [← hb1_eq]; exact hsp_b1)
          (by rw [← ha2_eq]; exact hsp_a2)
          (by simpa [hb1_eq, ha2_eq] using hturn)
        exact False.elim (Bool.false_ne_true (h_nb1a2.symm.trans hadj_ba))
      · exact ht
      · subst ht
        have hd_b2 := (hp2.2 (m2 - 1) (by omega)).2
        have hidx_b2 : rot[(m1 + 1) + (m2 - 1)]'(by dsimp only [m1, m2] at hrot_total; omega) =
            rot[m1 + m2]'(by dsimp only [m1, m2] at hrot_total; omega) := by congr 1; omega
        rw [hidx_b2] at hd_b2
        have hturn : baseDart = (nodePermOriented T orient).f
            (canonCartDart T deg refl d0 cd fu
              (getImgNat img (rot[m1 + m2]'(by dsimp only [m1, m2] at hrot_total; omega) + 1))) := by
          rw [hd_b2, ht_eq, ← _root_.Hypermap.Perm.iter_add]
          change _ = (nodePermOriented T orient).f
            (_root_.Hypermap.Perm.iter (nodePermOriented T orient) (m2 - 1 + (m1 + 2)) baseDart)
          have harith2 : m2 - 1 + (m1 + 2) + 1 = rot.length := by
            dsimp only [m1, m2] at hrot_total; omega
          have hf_iter : (nodePermOriented T orient).f
              (_root_.Hypermap.Perm.iter (nodePermOriented T orient) (m2 - 1 + (m1 + 2)) baseDart) =
              _root_.Hypermap.Perm.iter (nodePermOriented T orient) rot.length baseDart := by
            rw [← harith2]; rfl
          rw [hf_iter, ← hdeg_b,
            perm_iter_nodePermOriented_deg_eq_self T darts h_all h_len orient baseDart]
        have hb2_r : c.ringSize ≤ b2 := by
          rw [← hb2_eq, ← hidx_b2]; exact hm2_sub (m2 - 1) (by omega)
        have hb2_n : b2 < c.totalNodes := by
          rw [← hb2_eq]
          exact (mem_rot_is_adj hh hlen hur hun hu_adj (k := k) (m := m1 + m2)
            (by dsimp only [m1, m2, rot] at hrot_total ⊢; omega)).1
        have ha1_r : c.ringSize ≤ a1 := by rw [← ha1_eq]; exact hm1_sub 0 (by omega)
        have ha1_n : a1 < c.totalNodes := by
          rw [← ha1_eq]
          exact (mem_rot_is_adj hh hlen hur hun hu_adj (k := k) (m := 0) h0_pos).1
        have hne_ba : b2 ≠ a1 := by
          rw [← hb2_eq, ← ha1_eq]
          intro heq
          have : m1 + m2 = 0 := nodup_getElem_inj hrot_nd
            (by dsimp only [m1, m2] at hrot_total; omega) h0_pos heq
          omega
        have hidx_a1 : rot[0 + 0]'(by omega) = rot[0]'h0_pos := rfl
        have hsp_a1 := (hp1.2 0 (by omega)).1
        rw [hidx_a1] at hsp_a1
        have hsp_b2 := (hp2.2 (m2 - 1) (by omega)).1
        rw [hidx_b2] at hsp_b2
        have hadj_ba := hadj_of_turn hb2_r hb2_n ha1_r ha1_n hne_ba
          (by rw [← hb2_eq]; exact hsp_b2)
          (by rw [← ha1_eq]; exact hsp_a1)
          (by simpa [baseDart, ha1_eq, hb2_eq] using hturn)
        exact False.elim (Bool.false_ne_true (h_nb2a1.symm.trans hadj_ba))
    refine ⟨hsame_b, hdeg_b, fun m hm hrm => ?_⟩
    by_cases hm1_lt : m < m1
    · have hms := hp1.2 m hm1_lt
      have hidx : rot[0 + m]'(by omega) = rot[m]'hm := by congr 1; omega
      simpa [baseDart, hidx] using hms
    · have hge_m1 : m1 ≤ m := by omega
      have hne_m1 : m ≠ m1 := by
        intro heq; subst heq
        have hget : rot[m1]'hm = x1 := by
          have happ : rot = ((p1 ++ [x1]) ++ p2) ++ [x2] := by simpa [List.append_assoc] using hrot_eq
          have hlt' : m1 < ((p1 ++ [x1]) ++ p2).length := by
            dsimp only [m1, m2] at *; simp only [List.length_append, List.length_cons, List.length_nil]; omega
          have hlt2 : m1 < (p1 ++ [x1]).length := by
            dsimp only [m1]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
          rw [List.getElem_of_eq happ hm, List.getElem_append_left hlt',
            List.getElem_append_left hlt2, List.getElem_append_right (by dsimp only [m1]; exact Nat.le_refl _)]
          simp [m1]
        rw [hget] at hrm; omega
      have hne_last : m ≠ m1 + m2 + 1 := by
        intro heq; subst heq
        have hget : rot[m1 + m2 + 1]'hm = x2 := by
          have happ : rot = ((p1 ++ [x1]) ++ p2) ++ [x2] := by simpa [List.append_assoc] using hrot_eq
          have hge2 : ((p1 ++ [x1]) ++ p2).length ≤ m1 + m2 + 1 := by
            dsimp only [m1, m2] at *; simp only [List.length_append, List.length_cons, List.length_nil]; omega
          rw [List.getElem_of_eq happ hm, List.getElem_append_right hge2]
          have hidx0 : m1 + m2 + 1 - ((p1 ++ [x1]) ++ p2).length = 0 := by
            dsimp only [m1, m2] at *; simp only [List.length_append, List.length_cons, List.length_nil]; omega
          simp only [hidx0]; rfl
        rw [hget] at hrm; omega
      have hs_lt : m - (m1 + 1) < m2 := by dsimp only [m1, m2] at hrot_total; omega
      obtain ⟨hsp_s, hd_s⟩ := hp2.2 (m - (m1 + 1)) hs_lt
      have hidx_eq : rot[(m1 + 1) + (m - (m1 + 1))]'(by dsimp only [m1, m2] at hrot_total; omega) =
          rot[m]'hm := by congr 1; omega
      have hd_s' : canonCartDart T deg refl d0 cd fu (getImgNat img (rot[m]'hm + 1)) =
          _root_.Hypermap.Perm.iter (nodePermOriented T orient) m baseDart := by
        rw [← hidx_eq, hd_s, ht_eq, ht_eq_m1_add_1, ← _root_.Hypermap.Perm.iter_add]
        have hidx : m - (m1 + 1) + (m1 + 1) = m := by omega
        rw [hidx]
      have hsp_s' : ∃ i, 1 ≤ i ∧ i ≤ deg ∧
          (spokeEdgeDart T deg refl d0 i (cd i) fu (getImgNat img (rot[m]'hm + 1))).isSome = true := by
        simpa [hidx_eq] using hsp_s
      exact ⟨hsp_s', hd_s'⟩

theorem triangulation_embedding_of_hasExactReducedAxle
    (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_all : ∀ d : T.Dart, d ∈ darts)
    (h_loopless : ∀ d : T.Dart, sameVertex T d (T.edge.f d) darts.length = false)
    (h_tri : ∀ d : T.Dart, d ∈ darts → faceDegree T d darts.length = 3)
    (h5_all : ∀ d : T.Dart, d ∈ darts → 5 ≤ nodeDegree T d darts.length)
    (refl : Bool) (d0 : T.Dart)
    (hdeg11 : nodeDegree T d0 darts.length ≤ 11)
    (hcw : CartwheelEmbedded T darts.length refl d0)
    (h_red : HasExactReducedAxle (nodeDegree T d0 darts.length)
      (cartDegOriented T darts.length (nodeDegree T d0 darts.length) refl d0)) :
    ∃ (h : Nat) (hh : h < 633),
      ∃ (e : TriangulationEmbedding
        (configOfRConf (parsedRConfList[h]'(Math.Unavoidability.parsedRConfList_length ▸ hh))) T darts),
        MatchesConfCycle
          (parsedRConfList[h]'(Math.Unavoidability.parsedRConfList_length ▸ hh)) T darts e := by
  classical
  have h_len : darts.length ≤ darts.length := Nat.le_refl _
  have h_tri3 : ∀ x : T.Dart, T.face.f (T.face.f (T.face.f x)) = x :=
    face_cube_of_faceDegree_eq_three T darts h_all h_tri
  let deg := nodeDegree T d0 darts.length
  let cd := cartDegOriented T darts.length deg refl d0
  have hdeg5 : 5 ≤ deg := h5_all d0 (h_all d0)
  have hcd0 : cd 0 = deg := Discharging.cartDegOriented_zero T darts.length deg refl d0
  have hmin5 : ∀ p, 1 ≤ p → p ≤ 5 * deg → 5 ≤ cd p := fun p _ _ => h5_all _ (h_all _)
  have h_cw_conf := hasExactReducedAxle_exact_intVert_deg deg cd hcd0 hmin5 h_red
  rcases h_cw_conf with ⟨cur, h, x_r, y_r, cw_root, img, hh, hm31, hroot, hchk, hexact⟩
  have hlen : h < parsedRConfList.length := by rw [Math.Unavoidability.parsedRConfList_length]; exact hh
  rcases checkIsoRec_true_unpack hchk with ⟨invMap, usedMask, hinit, hspoke, hvert, hindu⟩
  let cw := !(getImgNat img 0).beq 0
  let orient := if cw = true then refl else !refl
  have hinit_s := initIsoVertsRec_sound hh hdeg11 hlen hinit
  have hmask_iff := hinit_s.1
  have himg_inj := hinit_s.2.2.2
  have hhdr := fastConf_equiv_header h hh
  have hadj := fastConf_equiv_adj h hh
  dsimp only at hhdr hadj
  let rc := parsedRConfList[h]'hlen
  let c := configOfRConf rc
  have hr_eq : c.ringSize = rc.r := hhdr.2.2.1
  have hn_eq : c.totalNodes = rc.n := hhdr.2.2.2.2.1
  have hint_eq : c.interiorSize = rc.n - rc.r := hhdr.2.2.2.1
  have hc_int_ge : 4 ≤ rc.n - rc.r := by rw [← hint_eq]; exact hhdr.2.2.2.2.2.2.2.1
  have hc_n : c.totalNodes = c.ringSize + c.interiorSize := by omega
  -- For each interior `u`, extract its rotated neighbor list and base dart
  have hk_exists : ∀ u (hur : c.ringSize ≤ u) (hun : u < c.totalNodes),
      ∃ k, ∃ hu_adj : u < rc.adj.size,
        k < (rc.adj[u]'hu_adj).toList.length ∧
        IntRunShape rc.r c (lookupFastConfRec h)
          ((lookupFastConfRec h).intVerts[u - c.ringSize]'(by
            rw [hhdr.2.2.2.2.2.2.2.2.2.2.1]; change u - c.ringSize < c.interiorSize; omega))
          ((rc.adj[u]'hu_adj).toList.drop k ++ (rc.adj[u]'hu_adj).toList.take k) := by
    intro u hur hun
    have hiu : u - c.ringSize < c.interiorSize := by omega
    obtain ⟨k, hk, hsh⟩ := fastConf_geom_int_runs h hh (u - c.ringSize) hiu
    have hu_adj : u < rc.adj.size := by rw [hhdr.2.2.2.2.2.2.2.2.2.2.2.1]; exact hun
    have hiu_add : c.ringSize + (u - c.ringSize) = u := by omega
    refine ⟨k, hu_adj, by simpa [c, rc, hiu_add] using hk, ?_⟩
    simpa [c, rc, hiu_add] using hsh
  let rotOf : Nat → List Nat := fun u =>
    if h_int : c.ringSize ≤ u ∧ u < c.totalNodes then
      let hex := hk_exists u h_int.1 h_int.2
      let k := Classical.choose hex
      let hu_adj := Classical.choose (Classical.choose_spec hex)
      (rc.adj[u]'hu_adj).toList.drop k ++ (rc.adj[u]'hu_adj).toList.take k
    else []
  let kOf : Nat → Nat := fun u =>
    if h_int : c.ringSize ≤ u ∧ u < c.totalNodes then
      Classical.choose (hk_exists u h_int.1 h_int.2)
    else 0
  let baseDartOf : Nat → T.Dart := fun u =>
    if h_int : c.ringSize ≤ u ∧ u < c.totalNodes then
      let rlist := rotOf u
      canonCartDart T deg refl d0 cd (getImgNat img (u + 1)) (getImgNat img (rlist[0]?.getD 0 + 1))
    else d0
  let dartFn : Nat → Nat → T.Dart := fun u v =>
    _root_.Hypermap.Perm.iter (nodePermOriented T orient) (posInList v (rotOf u)) (baseDartOf u)
  let repFn : Nat → T.Dart := fun x =>
    if hx : x < c.ringSize then
      let hx' : x < rc.r := hr_eq ▸ hx
      let hx_adj : x < rc.adj.size := by rw [hhdr.2.2.2.2.2.2.2.2.2.2.2.1, hc_n]; omega
      let fans := ((rc.adj[x]'hx_adj).toList.drop 1).dropLast
      T.edge.f (dartFn (fans[0]?.getD 0) x)
    else baseDartOf x
  have hrot_facts : ∀ u (hur : c.ringSize ≤ u) (hun : u < c.totalNodes),
      ∃ hu_adj : u < rc.adj.size,
        kOf u < (rc.adj[u]'hu_adj).toList.length ∧
        rotOf u = (rc.adj[u]'hu_adj).toList.drop (kOf u) ++
          (rc.adj[u]'hu_adj).toList.take (kOf u) ∧
        0 < (rotOf u).length ∧
        sameVertex T (baseDartOf u) (cartDartOriented T deg refl d0 (getImgNat img (u + 1)))
          darts.length = true ∧
        nodeDegree T (baseDartOf u) darts.length = (rotOf u).length ∧
        (rotOf u).Nodup ∧
        List.Perm (rotOf u) (rc.adj[u]'hu_adj).toList ∧
        ∀ m (hm : m < (rotOf u).length), c.ringSize ≤ (rotOf u)[m]'hm →
          (∃ i, 1 ≤ i ∧ i ≤ deg ∧
            (spokeEdgeDart T deg refl d0 i (cd i) (getImgNat img (u + 1))
              (getImgNat img ((rotOf u)[m]'hm + 1))).isSome = true) ∧
          canonCartDart T deg refl d0 cd (getImgNat img (u + 1))
            (getImgNat img ((rotOf u)[m]'hm + 1)) =
            _root_.Hypermap.Perm.iter (nodePermOriented T orient) m (baseDartOf u) := by
    intro u hur hun
    have h_int : c.ringSize ≤ u ∧ u < c.totalNodes := ⟨hur, hun⟩
    have hex := hk_exists u hur hun
    let k := Classical.choose hex
    have hk_spec := Classical.choose_spec hex
    let hu_adj := Classical.choose hk_spec
    have ⟨hk_lt, hsh⟩ := Classical.choose_spec hk_spec
    have hkOf_eq : kOf u = k := by simp [kOf, h_int]; rfl
    have hrot_eq : rotOf u =
        (rc.adj[u]'hu_adj).toList.drop k ++ (rc.adj[u]'hu_adj).toList.take k := by
      simp [rotOf, h_int]; rfl
    have hinv_u := intVert_of_ge_ring hh hlen hur hun
    obtain ⟨iu, hiu, hiu_fc, _, _, _⟩ := hinv_u
    have hiv := fastConf_equiv_intVerts h hh iu hiu
    have hlen_ge5 : 5 ≤ (rc.adj[u]'hu_adj).toList.length := by
      have hiu_eq : c.ringSize + iu = u := by omega
      have : ((lookupFastConfRec h).intVerts[iu]'hiu_fc).d = (rc.adj[u]'hu_adj).toList.length := by
        simpa [c, rc, hiu_eq, Array.length_toList] using hiv.2.1
      have : 5 ≤ ((lookupFastConfRec h).intVerts[iu]'hiu_fc).d := hiv.2.2.1
      omega
    have hrot_len : (rotOf u).length = (rc.adj[u]'hu_adj).toList.length := by
      rw [hrot_eq]; exact rotateList_length _ k
    have h0_pos : 0 < (rotOf u).length := by omega
    have hmain := int_nbr_canonCartDart_eq hh darts h_all h_tri3 refl d0 hdeg5 hdeg11 hmin5 hcw
      cw hmask_iff himg_inj hinit hspoke hindu hm31 hexact hvert hlen hur hun hu_adj hk_lt hsh
    have hbase_eq : baseDartOf u =
        canonCartDart T deg refl d0 cd (getImgNat img (u + 1))
          (getImgNat img (((rc.adj[u]'hu_adj).toList.drop k ++
            (rc.adj[u]'hu_adj).toList.take k)[0]'(by rw [← hrot_eq]; exact h0_pos) + 1)) := by
      simp only [baseDartOf, h_int, ← hrot_eq]
      rw [List.getElem?_eq_getElem h0_pos]
      rfl
    have hnd : (rotOf u).Nodup := by
      rw [hrot_eq]; exact rotateList_nodup (hadj.1 u hun).1 k
    have hperm : List.Perm (rotOf u) (rc.adj[u]'hu_adj).toList := by
      rw [hrot_eq]; exact rotateList_perm _ k
    have h1 : sameVertex T (baseDartOf u)
        (cartDartOriented T deg refl d0 (getImgNat img (u + 1))) darts.length = true := by
      rw [hbase_eq]; exact hmain.1
    have h2 : nodeDegree T (baseDartOf u) darts.length = (rotOf u).length := by
      calc nodeDegree T (baseDartOf u) darts.length
          = ((rc.adj[u]'hu_adj).toList.drop k ++ (rc.adj[u]'hu_adj).toList.take k).length := by
            rw [hbase_eq]; exact hmain.2.1
        _ = (rotOf u).length := by rw [hrot_eq]
    refine ⟨hu_adj, by rw [hkOf_eq]; exact hk_lt, by rw [hkOf_eq]; exact hrot_eq, h0_pos, h1, h2, hnd, hperm, ?_⟩
    · intro m hm hrm
      have hm' : m < ((rc.adj[u]'hu_adj).toList.drop k ++
          (rc.adj[u]'hu_adj).toList.take k).length := by rw [← hrot_eq]; exact hm
      have h_idx_eq : ((rc.adj[u]'hu_adj).toList.drop k ++
          (rc.adj[u]'hu_adj).toList.take k)[m]'hm' = (rotOf u)[m]'hm :=
        List.getElem_of_eq hrot_eq.symm hm'
      have hrm' : c.ringSize ≤ ((rc.adj[u]'hu_adj).toList.drop k ++
          (rc.adj[u]'hu_adj).toList.take k)[m]'hm' := by rw [h_idx_eq]; exact hrm
      obtain ⟨hsp, hcan⟩ := hmain.2.2 m hm' hrm'
      rw [h_idx_eq] at hsp hcan
      refine ⟨hsp, ?_⟩
      rw [hbase_eq]; exact hcan
  have hdart_eq_canon : ∀ u (hur : c.ringSize ≤ u) (hun : u < c.totalNodes)
      v (hvr : c.ringSize ≤ v) (hvn : v < c.totalNodes) (hadj_uv : c.adj u v = true),
      dartFn u v = canonCartDart T deg refl d0 cd (getImgNat img (u + 1)) (getImgNat img (v + 1)) ∧
      (∃ i, 1 ≤ i ∧ i ≤ deg ∧
        (spokeEdgeDart T deg refl d0 i (cd i) (getImgNat img (u + 1)) (getImgNat img (v + 1))).isSome = true) := by
    intro u hur hun v hvr hvn hadj_uv
    obtain ⟨hu_adj, _, _, _, _, _, hnd, hperm, hall⟩ := hrot_facts u hur hun
    have hv_mem : v ∈ (rc.adj[u]'hu_adj).toList := by
      have hadj_c := hadj_uv
      rw [hadj.2.1 u hun v hvn, List.contains_eq_mem, decide_eq_true_eq] at hadj_c
      exact hadj_c
    have hv_rot : v ∈ rotOf u := hperm.mem_iff.mpr hv_mem
    obtain ⟨m, hm, hm_eq⟩ := List.mem_iff_getElem.mp hv_rot
    have hpos : posInList v (rotOf u) = m := by rw [← hm_eq]; exact posInList_getElem hnd hm
    have hrm : c.ringSize ≤ (rotOf u)[m]'hm := by rw [hm_eq]; exact hvr
    obtain ⟨hsp, hcan⟩ := hall m hm hrm
    rw [hm_eq] at hcan hsp
    have hdart_def : dartFn u v = _root_.Hypermap.Perm.iter (nodePermOriented T orient) m (baseDartOf u) := by
      simp [dartFn, hpos]
    exact ⟨hdart_def.trans hcan.symm, hsp⟩
  have hint_same_vertex_fn : ∀ u (hur : c.ringSize ≤ u) (hun : u < c.totalNodes)
      v (hvn : v < c.totalNodes) (hadj_uv : c.adj u v = true),
      sameVertex T (dartFn u v) (repFn u) darts.length = true := by
    intro u hur hun v hvn _
    have hnot : ¬ (u < c.ringSize) := by omega
    simp only [repFn, hnot, dite_false, dartFn]
    exact sameVertex_iter_permOriented T darts h_all h_len orient (posInList v (rotOf u)) (baseDartOf u)
  have hint_edge_flip_fn : ∀ u (hur : c.ringSize ≤ u) (hun : u < c.totalNodes)
      v (hvr : c.ringSize ≤ v) (hvn : v < c.totalNodes) (hadj_uv : c.adj u v = true),
      T.edge.f (dartFn u v) = dartFn v u := by
    intro u hur hun v hvr hvn hadj_uv
    have hadj_vu : c.adj v u = true := by
      rw [← (hadj.2.2.1 u hun v hvn).1]; exact hadj_uv
    obtain ⟨hduv, i, hi1, hideg, hsp⟩ := hdart_eq_canon u hur hun v hvr hvn hadj_uv
    obtain ⟨hdvu, _⟩ := hdart_eq_canon v hvr hvn u hur hun hadj_vu
    have hedge := (canonCartDart_edge_of_spokeSome T darts h_all h_len h_tri3 refl d0 hdeg5 hcw
      hi1 hideg hsp).2.2.2.2.2.2.2
    rw [hduv, hdvu, hedge]
  have hint_distinct_fn : ∀ u1 (hu1r : c.ringSize ≤ u1) (hu1n : u1 < c.totalNodes)
      u2 (hu2r : c.ringSize ≤ u2) (hu2n : u2 < c.totalNodes) (hne : u1 ≠ u2),
      sameVertex T (repFn u1) (repFn u2) darts.length = false := by
    intro u1 hu1r hu1n u2 hu2r hu2n hne
    have hnot1 : ¬ (u1 < c.ringSize) := by omega
    have hnot2 : ¬ (u2 < c.ringSize) := by omega
    simp only [repFn, hnot1, hnot2, dite_false]
    obtain ⟨hu1_adj, _, _, hu1_pos, hu1_sv, _, _, _, hu1_all⟩ := hrot_facts u1 hu1r hu1n
    obtain ⟨hu2_adj, _, _, hu2_pos, hu2_sv, _, _, _, hu2_all⟩ := hrot_facts u2 hu2r hu2n
    -- Obtain active positions via first element of rotOf
    have hr1 : c.ringSize ≤ (rotOf u1)[0]'hu1_pos := by
      have hk_sh := hk_exists u1 hu1r hu1n
      let k1' := Classical.choose hk_sh
      have hsh1 := (Classical.choose_spec (Classical.choose_spec hk_sh)).2
      have hrot1_eq' : rotOf u1 =
          (rc.adj[u1]'hu1_adj).toList.drop k1' ++ (rc.adj[u1]'hu1_adj).toList.take k1' := by
        simp [rotOf, hu1r, hu1n]; rfl
      cases hsh1 with
      | allInterior hall_int _ =>
        have : (rotOf u1)[0]'hu1_pos ∈
            (rc.adj[u1]'hu1_adj).toList.drop k1' ++ (rc.adj[u1]'hu1_adj).toList.take k1' := by
          rw [← hrot1_eq']; exact List.getElem_mem hu1_pos
        have := hall_int _ this; omega
      | @oneRingRun p1 _ hreq hp1l _ hp1i _ =>
        have hget : (rotOf u1)[0]'hu1_pos = p1[0]'(by omega) := by
          rw [List.getElem_of_eq (hrot1_eq'.trans hreq) hu1_pos, List.getElem_append_left (by omega)]
        rw [hget]; have := hp1i _ (List.getElem_mem (l := p1) (n := 0) (by omega)); omega
      | @twoRingGaps p1 p2 x1 x2 hreq hp1l _ _ _ _ _ hp1i _ _ _ =>
        have hget : (rotOf u1)[0]'hu1_pos = p1[0]'(by omega) := by
          have happ : rotOf u1 = p1 ++ ([x1] ++ p2 ++ [x2]) := by
            rw [hrot1_eq', hreq]; simp only [List.append_assoc]
          rw [List.getElem_of_eq happ hu1_pos, List.getElem_append_left (by omega)]
        rw [hget]; have := hp1i _ (List.getElem_mem (l := p1) (n := 0) (by omega)); omega
    have hr2 : c.ringSize ≤ (rotOf u2)[0]'hu2_pos := by
      have hk_sh := hk_exists u2 hu2r hu2n
      let k2' := Classical.choose hk_sh
      have hsh2 := (Classical.choose_spec (Classical.choose_spec hk_sh)).2
      have hrot2_eq' : rotOf u2 =
          (rc.adj[u2]'hu2_adj).toList.drop k2' ++ (rc.adj[u2]'hu2_adj).toList.take k2' := by
        simp [rotOf, hu2r, hu2n]; rfl
      cases hsh2 with
      | allInterior hall_int _ =>
        have : (rotOf u2)[0]'hu2_pos ∈
            (rc.adj[u2]'hu2_adj).toList.drop k2' ++ (rc.adj[u2]'hu2_adj).toList.take k2' := by
          rw [← hrot2_eq']; exact List.getElem_mem hu2_pos
        have := hall_int _ this; omega
      | @oneRingRun p1 _ hreq hp1l _ hp1i _ =>
        have hget : (rotOf u2)[0]'hu2_pos = p1[0]'(by omega) := by
          rw [List.getElem_of_eq (hrot2_eq'.trans hreq) hu2_pos, List.getElem_append_left (by omega)]
        rw [hget]; have := hp1i _ (List.getElem_mem (l := p1) (n := 0) (by omega)); omega
      | @twoRingGaps p1 p2 x1 x2 hreq hp1l _ _ _ _ _ hp1i _ _ _ =>
        have hget : (rotOf u2)[0]'hu2_pos = p1[0]'(by omega) := by
          have happ : rotOf u2 = p1 ++ ([x1] ++ p2 ++ [x2]) := by
            rw [hrot2_eq', hreq]; simp only [List.append_assoc]
          rw [List.getElem_of_eq happ hu2_pos, List.getElem_append_left (by omega)]
        rw [hget]; have := hp1i _ (List.getElem_mem (l := p1) (n := 0) (by omega)); omega
    obtain ⟨⟨i1, hi11, hi1d, hsp1⟩, _⟩ := hu1_all 0 hu1_pos hr1
    obtain ⟨⟨i2, hi21, hi2d, hsp2⟩, _⟩ := hu2_all 0 hu2_pos hr2
    have hac1 := (canonCartDart_edge_of_spokeSome T darts h_all h_len h_tri3 refl d0 hdeg5 hcw
      hi11 hi1d hsp1).2.2.2.1
    have hac2 := (canonCartDart_edge_of_spokeSome T darts h_all h_len h_tri3 refl d0 hdeg5 hcw
      hi21 hi2d hsp2).2.2.2.1
    obtain ⟨iv1_i, _, hiv1_fc, hiv1_mem, hiv1_u, _⟩ := intVert_of_ge_ring hh hlen hu1r hu1n
    obtain ⟨iv2_i, _, hiv2_fc, hiv2_mem, hiv2_u, _⟩ := intVert_of_ge_ring hh hlen hu2r hu2n
    have hne_iv : ((lookupFastConfRec h).intVerts[iv1_i]'hiv1_fc).u ≠
        ((lookupFastConfRec h).intVerts[iv2_i]'hiv2_fc).u := by
      rw [hiv1_u, hiv2_u]; omega
    have hne_f := himg_inj _ hiv1_mem _ hiv2_mem hne_iv
    rw [hiv1_u, hiv2_u] at hne_f
    have hdisj := hcw.1 _ _ hac1 hac2 hne_f
    cases h_eq : sameVertex T (baseDartOf u1) (baseDartOf u2) darts.length with
    | false => rfl
    | true =>
      have hu1_sv' := hu1_sv
      rw [sameVertex_symm_of_complete T darts h_all h_len] at hu1_sv'
      have hmid := sameVertex_trans_of_complete T darts h_all h_len hu1_sv' h_eq
      have hbad := sameVertex_trans_of_complete T darts h_all h_len hmid hu2_sv
      exact absurd (hdisj.symm.trans hbad) (by decide)
  have hmatches_fn : ∀ u, rc.r ≤ u → u < rc.n →
      ∀ hu : u < rc.adj.size,
        let nbrs := (rc.adj[u]'hu).toList
        ∀ (j : Nat) (hj : j < nbrs.length),
          let j1 := (j + 1) % nbrs.length
          have hj1 : j1 < nbrs.length := Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le _) hj)
          dartFn u (nbrs[j1]'hj1) = (nodePermOriented T orient).f (dartFn u (nbrs[j]'hj)) := by
    intro u hur hun hu nbrs j hj j1 hj1
    have hur' : c.ringSize ≤ u := by omega
    have hun' : u < c.totalNodes := by omega
    obtain ⟨hu_adj, hk_lt, hrot_eq, h0_pos, _, hdeg_b, hnd, hperm, _⟩ := hrot_facts u hur' hun'
    have hlen_eq : nbrs.length = (rotOf u).length := hperm.length_eq.symm
    have hnbrs_eq : (rc.adj[u]'hu_adj).toList = nbrs := rfl
    let k := kOf u
    have hk_lt_nbrs : k < nbrs.length := by simpa [k, nbrs] using hk_lt
    have hm_lt : (j + nbrs.length - k) % nbrs.length < (rotOf u).length := by
      rw [← hlen_eq]; exact Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le j) hj)
    have hm1_lt : (j1 + nbrs.length - k) % nbrs.length < (rotOf u).length := by
      rw [← hlen_eq]; exact Nat.mod_lt _ (Nat.lt_of_le_of_lt (Nat.zero_le j) hj)
    let m := (j + nbrs.length - k) % nbrs.length
    let m1 := (j1 + nbrs.length - k) % nbrs.length
    have hrot_m : (rotOf u)[m]'hm_lt = nbrs[j]'hj := by
      rw [List.getElem_of_eq hrot_eq (hrot_eq ▸ hm_lt)]
      rw [rotateList_getElem (rc.adj[u]'hu_adj).toList hk_lt (hrot_eq ▸ hm_lt)]
      have harith : (k + m) % nbrs.length = j := by
        dsimp only [m]
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have hsum : k + (j + nbrs.length - k) = j + nbrs.length := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hj]
      simp only [hnbrs_eq] at harith ⊢
      congr 1
    have hrot_m1 : (rotOf u)[m1]'hm1_lt = nbrs[j1]'hj1 := by
      rw [List.getElem_of_eq hrot_eq (hrot_eq ▸ hm1_lt)]
      rw [rotateList_getElem (rc.adj[u]'hu_adj).toList hk_lt (hrot_eq ▸ hm1_lt)]
      have harith : (k + m1) % nbrs.length = j1 := by
        dsimp only [m1]
        rw [Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
        have hsum : k + (j1 + nbrs.length - k) = j1 + nbrs.length := by omega
        rw [hsum, Nat.add_mod_right, Nat.mod_eq_of_lt hj1]
      simp only [hnbrs_eq] at harith ⊢
      congr 1
    have hpos_m : posInList (nbrs[j]'hj) (rotOf u) = m := by
      rw [← hrot_m]; exact posInList_getElem hnd hm_lt
    have hpos_m1 : posInList (nbrs[j1]'hj1) (rotOf u) = m1 := by
      rw [← hrot_m1]; exact posInList_getElem hnd hm1_lt
    have hm1_mod : m1 = (m + 1) % (rotOf u).length := by
      rw [← hlen_eq]
      have h1 : (j1 + nbrs.length - k) % nbrs.length = ((j + 1) + nbrs.length - k) % nbrs.length := by
        have : j1 = (j + 1) % nbrs.length := rfl
        rw [this]
        by_cases hj_next : j + 1 < nbrs.length
        · have hm' : (j + 1) % nbrs.length = j + 1 := Nat.mod_eq_of_lt hj_next
          rw [hm']
        · have hj_last : j + 1 = nbrs.length := by omega
          rw [hj_last, Nat.mod_self, Nat.zero_add]
          have hmod_add : (nbrs.length + nbrs.length - k) % nbrs.length =
              ((nbrs.length - k) + nbrs.length) % nbrs.length := by
            have : nbrs.length + nbrs.length - k = (nbrs.length - k) + nbrs.length := by omega
            rw [this]
          rw [hmod_add, Nat.add_mod_right]
      dsimp only [m, m1]
      rw [h1]
      have harith : (j + 1) + nbrs.length - k = (j + nbrs.length - k) + 1 := by omega
      rw [harith, Nat.mod_add_mod]
    simp only [dartFn, hpos_m, hpos_m1]
    by_cases hm_next : m + 1 < (rotOf u).length
    · have hm1_eq : m1 = m + 1 := by rw [hm1_mod, Nat.mod_eq_of_lt hm_next]
      rw [hm1_eq]
      rfl
    · have hm_last : m + 1 = (rotOf u).length := by omega
      have hm1_eq : m1 = 0 := by rw [hm1_mod, hm_last, Nat.mod_self]
      rw [hm1_eq]
      have hf : (nodePermOriented T orient).f
          (_root_.Hypermap.Perm.iter (nodePermOriented T orient) m (baseDartOf u)) =
          _root_.Hypermap.Perm.iter (nodePermOriented T orient) (m + 1) (baseDartOf u) := rfl
      rw [hf, hm_last, ← hdeg_b,
        perm_iter_nodePermOriented_deg_eq_self T darts h_all h_len orient (baseDartOf u)]
      rfl
  -- Helper: fan membership of any interior neighbor of ring vertex x
  have hfan_same_vertex : ∀ x (hx : x < c.ringSize) (hx_adj : x < rc.adj.size),
      let fans := ((rc.adj[x]'hx_adj).toList.drop 1).dropLast
      ∀ (k : Nat) (hk : k < fans.length),
        c.ringSize ≤ fans[k]'hk ∧ fans[k]'hk < c.totalNodes ∧
        sameVertex T (T.edge.f (dartFn (fans[k]'hk) x)) (repFn x) darts.length = true := by
    intro x hx hx_adj fans k hk
    have hrf := fastConf_geom_ring_fans h hh x (hr_eq ▸ hx)
    have hfans_ne : fans ≠ [] := hrf.1
    have hfans_pos : 0 < fans.length :=
      Nat.pos_of_ne_zero (fun h0 => hfans_ne (List.eq_nil_of_length_eq_zero h0))
    have hx_eq : repFn x = T.edge.f (dartFn (fans[0]'hfans_pos) x) := by
      simp only [repFn, hx, dite_true]
      change T.edge.f (dartFn (fans[0]?.getD 0) x) = _
      rw [List.getElem?_eq_getElem hfans_pos]
      rfl
    have hrf_consec := hrf.2.2.2.2
    have hbound : ∀ k (hk : k < fans.length),
        c.ringSize ≤ fans[k]'hk ∧ fans[k]'hk < c.totalNodes := by
      intro k hk
      have hmem1 : fans[k]'hk ∈ (rc.adj[x]'hx_adj).toList :=
        List.mem_of_mem_drop (mem_of_mem_dropLast (List.getElem_mem hk))
      have hx_tot : x < (configOfRConf (parsedRConfList[h]'hlen)).totalNodes := by
        change x < c.totalNodes; omega
      have hlt_n : fans[k]'hk < c.totalNodes := ((hadj.1 x hx_tot).2 _ hmem1).1
      refine ⟨?_, hlt_n⟩
      have hu1_ge : ∃ iv_k, iv_k ∈ (lookupFastConfRec h).intVerts ∧ iv_k.u = fans[k]'hk + 1 := by
        by_cases hk0 : k = 0
        · subst hk0
          have hhd := List.head?_eq_some_head hfans_ne
          rw [List.head_eq_getElem] at hhd
          obtain ⟨iv1, hiv1, hiv1_u, _⟩ := hrf.2.2.1 _ hhd
          exact ⟨iv1, hiv1, hiv1_u⟩
        · have hk1 : (k - 1) + 1 < fans.length := by omega
          obtain ⟨_, _, ivk1, hivk1, _, hivk1_u, _⟩ := hrf_consec (k - 1) hk1
          have hk_eq : (k - 1) + 1 = k := by omega
          simp only [hk_eq] at hivk1_u
          exact ⟨ivk1, hivk1, hivk1_u⟩
      obtain ⟨iv_k, hiv_mem, hiv_u⟩ := hu1_ge
      obtain ⟨iu_k, hiu_k, hiu_fc⟩ := List.mem_iff_getElem.mp hiv_mem
      have hiu_c : iu_k < c.interiorSize := by
        rw [← hhdr.2.2.2.2.2.2.2.2.2.2.1]; exact hiu_k
      have hiv_s := fastConf_equiv_intVerts h hh iu_k hiu_c
      have : iv_k.u = c.ringSize + iu_k + 1 := by
        have := hiv_s.1
        simpa [← hiu_fc] using this
      omega
    have hsame_0 : ∀ k (hk : k < fans.length),
        sameVertex T (T.edge.f (dartFn (fans[k]'hk) x)) (repFn x) darts.length = true := by
      intro k
      induction k with
      | zero =>
        intro hk
        rw [hx_eq]
        exact sameVertex_refl T darts.length _
      | succ k ih =>
        intro hk
        have hk_prev : k < fans.length := by omega
        have hprev_sv := ih hk_prev
        obtain ⟨uk_r, uk_n⟩ := hbound k hk_prev
        obtain ⟨uk1_r, uk1_n⟩ := hbound (k + 1) hk
        obtain ⟨ivk, hivk_mem, ivk1, hivk1_mem, hivk_u, hivk1_u, hcp_k, hcp_k1⟩ :=
          hrf_consec k hk
        have hiu_k : fans[k]'hk_prev - c.ringSize < c.interiorSize := by omega
        have hiu_k1 : fans[k + 1]'hk - c.ringSize < c.interiorSize := by omega
        have hiu_k_fc : fans[k]'hk_prev - c.ringSize < (lookupFastConfRec h).intVerts.length := by
          rw [hhdr.2.2.2.2.2.2.2.2.2.2.1]; exact hiu_k
        have hiu_k1_fc : fans[k + 1]'hk - c.ringSize < (lookupFastConfRec h).intVerts.length := by
          rw [hhdr.2.2.2.2.2.2.2.2.2.2.1]; exact hiu_k1
        have hivk_eq : ((lookupFastConfRec h).intVerts[fans[k]'hk_prev - c.ringSize]'hiu_k_fc) = ivk := by
          obtain ⟨i_k, hi_k_lt, hi_k_eq⟩ := List.mem_iff_getElem.mp hivk_mem
          have hiu_c_lt : i_k < c.interiorSize := by
            rw [← hhdr.2.2.2.2.2.2.2.2.2.2.1]; exact hi_k_lt
          have hiv_i := fastConf_equiv_intVerts h hh i_k hiu_c_lt
          have hu_eq1 : (lookupFastConfRec h).intVerts[i_k].u = c.ringSize + i_k + 1 := hiv_i.1
          rw [hi_k_eq] at hu_eq1
          rw [hu_eq1] at hivk_u
          have hivk_u' : c.ringSize + i_k + 1 = fans[k]'hk_prev + 1 := hivk_u
          have hi_eq : i_k = fans[k]'hk_prev - c.ringSize := by omega
          subst hi_eq; exact hi_k_eq
        have hivk1_eq : ((lookupFastConfRec h).intVerts[fans[k + 1]'hk - c.ringSize]'hiu_k1_fc) = ivk1 := by
          obtain ⟨i_k1, hi_k1_lt, hi_k1_eq⟩ := List.mem_iff_getElem.mp hivk1_mem
          have hiu_c_lt : i_k1 < c.interiorSize := by
            rw [← hhdr.2.2.2.2.2.2.2.2.2.2.1]; exact hi_k1_lt
          have hiv_i1 := fastConf_equiv_intVerts h hh i_k1 hiu_c_lt
          have hu_eq1 : (lookupFastConfRec h).intVerts[i_k1].u = c.ringSize + i_k1 + 1 := hiv_i1.1
          rw [hi_k1_eq] at hu_eq1
          rw [hu_eq1] at hivk1_u
          have hivk1_u' : c.ringSize + i_k1 + 1 = fans[k + 1]'hk + 1 := hivk1_u
          have hi_eq : i_k1 = fans[k + 1]'hk - c.ringSize := by omega
          subst hi_eq; exact hi_k1_eq
        have hsum_k : (configOfRConf (parsedRConfList[h]'hlen)).ringSize +
            (fans[k]'hk_prev - c.ringSize) = fans[k]'hk_prev := by
          change c.ringSize + (fans[k]'hk_prev - c.ringSize) = fans[k]'hk_prev; omega
        have hsum_k1 : (configOfRConf (parsedRConfList[h]'hlen)).ringSize +
            (fans[k + 1]'hk - c.ringSize) = fans[k + 1]'hk := by
          change c.ringSize + (fans[k + 1]'hk - c.ringSize) = fans[k + 1]'hk; omega
        have hstep1 : dartFn (fans[k]'hk_prev) x =
            (nodePermOriented T orient).f (dartFn (fans[k]'hk_prev) (fans[k + 1]'hk)) := by
          have hm_fn := matchesConfCycleFn_of_mem_cyc hh dartFn orient hlen hmatches_fn
            hiu_k hiu_k_fc (hivk_eq ▸ hcp_k)
          rw [hsum_k] at hm_fn
          simpa only [Nat.add_sub_cancel] using hm_fn
        have hstep2 : dartFn (fans[k + 1]'hk) (fans[k]'hk_prev) =
            (nodePermOriented T orient).f (dartFn (fans[k + 1]'hk) x) := by
          have hm_fn := matchesConfCycleFn_of_mem_cyc hh dartFn orient hlen hmatches_fn
            hiu_k1 hiu_k1_fc (hivk1_eq ▸ hcp_k1)
          rw [hsum_k1] at hm_fn
          simpa only [Nat.add_sub_cancel] using hm_fn
        have huk_rc_n : fans[k]'hk_prev < rc.adj.size := by
          rw [hhdr.2.2.2.2.2.2.2.2.2.2.2.1]; exact uk_n
        have hadj_uk_uk1 : c.adj (fans[k]'hk_prev) (fans[k + 1]'hk) = true := by
          have hiv_k := fastConf_equiv_intVerts h hh (fans[k]'hk_prev - c.ringSize) hiu_k
          have hcyc_k := hiv_k.2.2.2.2.2.2.2.2.1
          have hcyc_len_k := hiv_k.2.2.2.2.2.2.2.1
          obtain ⟨jc, hjc_lt, hjc_eq⟩ := List.mem_iff_getElem.mp (hivk_eq ▸ hcp_k)
          have hspec := hcyc_k jc (hcyc_len_k ▸ hjc_lt) hjc_lt
          rw [hjc_eq] at hspec
          have hi_idx : (configOfRConf (parsedRConfList[h]'hlen)).ringSize +
              (fans[k]'hk_prev - c.ringSize) < (parsedRConfList[h]'hlen).adj.size := by
            change _ < rc.adj.size; rw [hsum_k]; exact huk_rc_n
          have hv1 : (List.drop 1 (parsedRConfList[h]'hlen).adj[x].toList).dropLast[k + 1]'hk =
              ((parsedRConfList[h]'hlen).adj[(configOfRConf (parsedRConfList[h]'hlen)).ringSize +
                (fans[k]'hk_prev - c.ringSize)]'hi_idx).toList[jc]'(hcyc_len_k ▸ hjc_lt) :=
            Nat.add_right_cancel (CycPair.mk.inj hspec).1
          have hmem_idx : fans[k + 1]'hk ∈
              ((parsedRConfList[h]'hlen).adj[(configOfRConf (parsedRConfList[h]'hlen)).ringSize +
                (fans[k]'hk_prev - c.ringSize)]'hi_idx).toList := by
            have hmem0 := List.getElem_mem (l := ((parsedRConfList[h]'hlen).adj[
              (configOfRConf (parsedRConfList[h]'hlen)).ringSize +
                (fans[k]'hk_prev - c.ringSize)]'hi_idx).toList) (hcyc_len_k ▸ hjc_lt)
            rw [← hv1] at hmem0
            exact hmem0
          have hmem_k1 : fans[k + 1]'hk ∈ (rc.adj[fans[k]'hk_prev]'huk_rc_n).toList := by
            simp only [hsum_k] at hmem_idx
            exact hmem_idx
          rw [hadj.2.1 _ uk_n _ uk1_n, List.contains_eq_mem]
          simpa [decide_eq_true_eq] using hmem_k1
        have hflip := hint_edge_flip_fn (fans[k]'hk_prev) uk_r uk_n (fans[k + 1]'hk) uk1_r uk1_n hadj_uk_uk1
        have hinv : dartFn (fans[k + 1]'hk) x =
            (nodePermOriented T orient).inv (T.edge.f (dartFn (fans[k]'hk_prev) (fans[k + 1]'hk))) := by
          rw [hflip, hstep2]
          exact ((nodePermOriented T orient).left_inv _).symm
        have heturn : T.edge.f (dartFn (fans[k + 1]'hk) x) =
            (nodePermOriented T orient).f (T.edge.f (dartFn (fans[k]'hk_prev) x)) := by
          rw [hinv, tri_fan_turn T h_tri3 orient, ← hstep1]
        have hsv_step : sameVertex T (T.edge.f (dartFn (fans[k + 1]'hk) x))
            (T.edge.f (dartFn (fans[k]'hk_prev) x)) darts.length = true := by
          rw [heturn]
          exact sameVertex_permOriented_f T darts h_all h_len orient _
        exact sameVertex_trans_of_complete T darts h_all h_len hsv_step hprev_sv
    exact ⟨(hbound k hk).1, (hbound k hk).2, hsame_0 k hk⟩
  have hdart_edge_sv : ∀ u, c.ringSize ≤ u → u < c.totalNodes →
      ∀ v, v < c.totalNodes → c.adj u v = true →
      sameVertex T (T.edge.f (dartFn u v)) (repFn v) darts.length = true := by
    intro u hur hun v hvn hadj_uv
    have hadj_vu : c.adj v u = true := by
      rw [← (hadj.2.2.1 u hun v hvn).1]; exact hadj_uv
    by_cases hv_r : v < c.ringSize
    · have hv_adj : v < rc.adj.size := by rw [hhdr.2.2.2.2.2.2.2.2.2.2.2.1]; exact hvn
      have hu_mem : u ∈ (rc.adj[v]'hv_adj).toList := by
        rw [hadj.2.1 v hvn u hun, List.contains_eq_mem, decide_eq_true_eq] at hadj_vu
        exact hadj_vu
      have hu_fans : u ∈ ((rc.adj[v]'hv_adj).toList.drop 1).dropLast :=
        ringAdj_int_in_fans hh hlen v (hr_eq ▸ hv_r) hv_adj u hu_mem (hr_eq ▸ hur)
      obtain ⟨kf, hkf, hkf_eq⟩ := List.mem_iff_getElem.mp hu_fans
      have hres := (hfan_same_vertex v hv_r hv_adj kf hkf).2.2
      rw [hkf_eq] at hres
      exact hres
    · have hvr : c.ringSize ≤ v := by omega
      rw [hint_edge_flip_fn u hur hun v hvr hvn hadj_uv]
      exact hint_same_vertex_fn v hvr hvn u hun hadj_vu
  have hmem_of_getLast? : ∀ {α : Type} {l : List α} {a : α}, l.getLast? = some a → a ∈ l := by
    intro α l a hl
    induction l with
    | nil => simp at hl
    | cons b tl ih =>
      cases tl with
      | nil => simp at hl; exact hl ▸ List.mem_cons_self
      | cons d_e tl' =>
        simp only [List.getLast?_cons_cons] at hl
        exact List.mem_cons_of_mem b (ih hl)
  have hadj_rep_edge_fn : ∀ i j, i < c.totalNodes → j < c.totalNodes → c.adj i j = true →
      areAdjacentVertices T (repFn i) (repFn j) darts.length = true := by
    have helper_ir : ∀ a b, a < c.totalNodes → b < c.totalNodes →
        c.ringSize ≤ a → c.adj a b = true →
        areAdjacentVertices T (repFn a) (repFn b) darts.length = true := by
      intro a b ha hb har hab
      exact areAdjacentVertices_of_dart T darts h_all h_len
        (hint_same_vertex_fn a har ha b hb hab)
        (hdart_edge_sv a har ha b hb hab)
    intro i j hi hj hadj_ij
    by_cases hir : c.ringSize ≤ i
    · exact helper_ir i j hi hj hir hadj_ij
    · by_cases hjr : c.ringSize ≤ j
      · have hadj_ji : c.adj j i = true := by
          rw [← (hadj.2.2.1 i hi j hj).1]; exact hadj_ij
        rw [areAdjacentVertices_symm T darts h_all h_len]
        exact helper_ir j i hj hi hjr hadj_ji
      · have hi_r : i < c.ringSize := by omega
        have hj_r : j < c.ringSize := by omega
        have hc_edge : ∀ x (hx : x < c.ringSize),
            let nextR := (x + 1) % c.ringSize
            areAdjacentVertices T (repFn x) (repFn nextR) darts.length = true := by
          intro x hx nextR
          have hx_rc : x < rc.r := hr_eq ▸ hx
          have hrf := fastConf_geom_ring_fans h hh x hx_rc
          have hxn : x < rc.adj.size := by
            rw [hhdr.2.2.2.2.2.2.2.2.2.2.2.1]; change x < c.totalNodes; omega
          have hnext_r : nextR < c.ringSize := Nat.mod_lt _ (by omega)
          have hnext_n : nextR < rc.adj.size := by
            rw [hhdr.2.2.2.2.2.2.2.2.2.2.2.1]; change nextR < c.totalNodes; omega
          let fans := ((rc.adj[x]'hxn).toList.drop 1).dropLast
          let nextFans := ((rc.adj[nextR]'hnext_n).toList.drop 1).dropLast
          have hfans_ne : fans ≠ [] := hrf.1
          have hfans_pos : 0 < fans.length :=
            Nat.pos_of_ne_zero (fun h0 => hfans_ne (List.eq_nil_of_length_eq_zero h0))
          have hhd : fans.head? = some (fans[0]'hfans_pos) := by
            have := List.head?_eq_some_head hfans_ne
            rwa [List.head_eq_getElem] at this
          obtain ⟨iv1, hiv1_mem, hiv1_u, hcp1⟩ := hrf.2.2.1 _ hhd
          obtain ⟨j_iv1, hj_iv1_lt, hj_iv1_eq⟩ := List.mem_iff_getElem.mp hiv1_mem
          have hj_iv1_c : j_iv1 < c.interiorSize := by
            rw [← hhdr.2.2.2.2.2.2.2.2.2.2.1]; exact hj_iv1_lt
          have hiv_j1 := fastConf_equiv_intVerts h hh j_iv1 hj_iv1_c
          have hu_eq1 : (lookupFastConfRec h).intVerts[j_iv1].u = c.ringSize + j_iv1 + 1 := hiv_j1.1
          rw [hj_iv1_eq] at hu_eq1
          have hu1_r : c.ringSize ≤ fans[0]'hfans_pos := (hfan_same_vertex x hx hxn 0 hfans_pos).1
          have hj_eq : j_iv1 = fans[0]'hfans_pos - c.ringSize := by
            rw [hu_eq1] at hiv1_u; omega
          subst hj_eq
          have hturn_step := matchesConfCycleFn_of_mem_cyc hh dartFn orient hlen hmatches_fn
            (by omega : fans[0]'hfans_pos - c.ringSize < c.interiorSize)
            (by rw [hhdr.2.2.2.2.2.2.2.2.2.2.1]; omega)
            (hj_iv1_eq ▸ hcp1)
          have hsum0 : (configOfRConf (parsedRConfList[h]'hlen)).ringSize +
              (fans[0]'hfans_pos - c.ringSize) = fans[0]'hfans_pos := by
            change c.ringSize + (fans[0]'hfans_pos - c.ringSize) = fans[0]'hfans_pos; omega
          rw [hsum0] at hturn_step
          have hnext_rc : nextR = (x + 1) % rc.r := by
            change (x + 1) % c.ringSize = (x + 1) % rc.r; rw [hr_eq]
          rw [← hnext_rc] at hturn_step
          have hturn : dartFn (fans[0]'hfans_pos) nextR =
              (nodePermOriented T orient).f (dartFn (fans[0]'hfans_pos) x) := by
            simpa only [Nat.add_sub_cancel] using hturn_step
          have hadj_e := areAdjacentVertices_of_tri_fan_turn darts h_all h_len h_tri3 orient hturn
          have hsv_x : sameVertex T (T.edge.f (dartFn (fans[0]'hfans_pos) x)) (repFn x)
              darts.length = true := (hfan_same_vertex x hx hxn 0 hfans_pos).2.2
          have hlast_next : nextFans.getLast? = some (fans[0]'hfans_pos) := by
            have h2 : nextFans.getLast? = fans.head? := hrf.2.1
            rw [h2, hhd]
          have hmem_next : fans[0]'hfans_pos ∈ nextFans := hmem_of_getLast? hlast_next
          obtain ⟨knf, hknf, hknf_eq⟩ := List.mem_iff_getElem.mp hmem_next
          have hsv_next : sameVertex T (T.edge.f (dartFn (fans[0]'hfans_pos) nextR)) (repFn nextR)
              darts.length = true := by
            have h5 := (hfan_same_vertex nextR hnext_r hnext_n knf hknf).2.2
            rw [hknf_eq] at h5
            exact h5
          rw [← areAdjacentVertices_congr T darts h_all h_len hsv_x hsv_next]
          exact hadj_e
        have hi_adj : i < rc.adj.size := by rw [hhdr.2.2.2.2.2.2.2.2.2.2.2.1]; exact hi
        have hj_mem : j ∈ (rc.adj[i]'hi_adj).toList := by
          rw [hadj.2.1 i hi j hj, List.contains_eq_mem, decide_eq_true_eq] at hadj_ij
          exact hadj_ij
        rcases ringAdj_consec hh hlen i (hr_eq ▸ hi_r) hi_adj j hj_mem (hr_eq ▸ hj_r) with hnext | hprev
        · have hnext' : j = (i + 1) % c.ringSize := by rw [hr_eq]; exact hnext
          rw [hnext']
          exact hc_edge i hi_r
        · have hprev' : i = (j + 1) % c.ringSize := by rw [hr_eq]; exact hprev
          rw [areAdjacentVertices_symm T darts h_all h_len, hprev']
          exact hc_edge j hj_r
  have hint_first_ge_ring : ∀ u (hur : c.ringSize ≤ u) (hun : u < c.totalNodes),
      ∃ h0_pos : 0 < (rotOf u).length, c.ringSize ≤ (rotOf u)[0]'h0_pos := by
    intro u hur hun
    obtain ⟨hu_adj, _, _, h0_pos, _, _, _, _, _⟩ := hrot_facts u hur hun
    refine ⟨h0_pos, ?_⟩
    have hk_sh := hk_exists u hur hun
    let k' := Classical.choose hk_sh
    have hsh' := (Classical.choose_spec (Classical.choose_spec hk_sh)).2
    have hrot_eq' : rotOf u =
        (rc.adj[u]'hu_adj).toList.drop k' ++ (rc.adj[u]'hu_adj).toList.take k' := by
      simp [rotOf, hur, hun]; rfl
    cases hsh' with
    | allInterior hall_int _ =>
      have : (rotOf u)[0]'h0_pos ∈
          (rc.adj[u]'hu_adj).toList.drop k' ++ (rc.adj[u]'hu_adj).toList.take k' := by
        rw [← hrot_eq']; exact List.getElem_mem h0_pos
      have := hall_int _ this; omega
    | @oneRingRun p1 _ hreq hp1l _ hp1i _ =>
      have hget : (rotOf u)[0]'h0_pos = p1[0]'(by omega) := by
        rw [List.getElem_of_eq (hrot_eq'.trans hreq) h0_pos, List.getElem_append_left (by omega)]
      rw [hget]; have := hp1i _ (List.getElem_mem (l := p1) (n := 0) (by omega)); omega
    | @twoRingGaps p1 p2 x1 x2 hreq hp1l _ _ _ _ _ hp1i _ _ _ =>
      have hget : (rotOf u)[0]'h0_pos = p1[0]'(by omega) := by
        have happ : rotOf u = p1 ++ ([x1] ++ p2 ++ [x2]) := by
          rw [hrot_eq', hreq]; simp only [List.append_assoc]
        rw [List.getElem_of_eq happ h0_pos, List.getElem_append_left (by omega)]
      rw [hget]; have := hp1i _ (List.getElem_mem (l := p1) (n := 0) (by omega)); omega
  have hint_active : ∀ u (hur : c.ringSize ≤ u) (hun : u < c.totalNodes),
      activeCartPos deg cd (getImgNat img (u + 1)) ∧
      sameVertex T (repFn u) (cartDartOriented T deg refl d0 (getImgNat img (u + 1))) darts.length = true ∧
      usedMask.testBit (getImgNat img (u + 1)) = true := by
    intro u hur hun
    obtain ⟨h0_pos, hr0⟩ := hint_first_ge_ring u hur hun
    obtain ⟨_, _, _, _, h_sv, _, _, _, hall⟩ := hrot_facts u hur hun
    obtain ⟨⟨i0, hi01, hi0d, hsp0⟩, _⟩ := hall 0 h0_pos hr0
    have hact := (canonCartDart_edge_of_spokeSome T darts h_all h_len h_tri3 refl d0 hdeg5 hcw
      hi01 hi0d hsp0).2.2.2.1
    have hnot : ¬ (u < c.ringSize) := by omega
    have h_sv' : sameVertex T (repFn u)
        (cartDartOriented T deg refl d0 (getImgNat img (u + 1))) darts.length = true := by
      simp only [repFn, hnot, dite_false]; exact h_sv
    obtain ⟨_, _, _, hiv_mem, hiv_u, _⟩ := intVert_of_ge_ring hh hlen hur hun
    have hbit : usedMask.testBit (getImgNat img (u + 1)) = true := by
      rw [hmask_iff]; exact ⟨_, hiv_mem, by rw [hiv_u]⟩
    exact ⟨hact, h_sv', hbit⟩
  have hint_img_ne : ∀ u1 (hu1r : c.ringSize ≤ u1) (hu1n : u1 < c.totalNodes)
      u2 (hu2r : c.ringSize ≤ u2) (hu2n : u2 < c.totalNodes),
      u1 ≠ u2 → getImgNat img (u1 + 1) ≠ getImgNat img (u2 + 1) := by
    intro u1 hu1r hu1n u2 hu2r hu2n hne
    obtain ⟨iv1_i, _, hiv1_fc, hiv1_mem, hiv1_u, _⟩ := intVert_of_ge_ring hh hlen hu1r hu1n
    obtain ⟨iv2_i, _, hiv2_fc, hiv2_mem, hiv2_u, _⟩ := intVert_of_ge_ring hh hlen hu2r hu2n
    have hne_iv : ((lookupFastConfRec h).intVerts[iv1_i]'hiv1_fc).u ≠
        ((lookupFastConfRec h).intVerts[iv2_i]'hiv2_fc).u := by
      rw [hiv1_u, hiv2_u]; omega
    have hne_f := himg_inj _ hiv1_mem _ hiv2_mem hne_iv
    rw [hiv1_u, hiv2_u] at hne_f
    exact hne_f
  let emb : TriangulationEmbedding
      (configOfRConf (parsedRConfList[h]'(Math.Unavoidability.parsedRConfList_length ▸ hh))) T darts :=
    { rep := repFn
      dart := dartFn
      orient := orient
      int_nonempty := by
        intro u hur hun
        obtain ⟨hu_adj, _, _, h0_pos, _, _, _, hperm, _⟩ := hrot_facts u hur hun
        have hmem_rot : (rotOf u)[0]'h0_pos ∈ rotOf u := List.getElem_mem h0_pos
        have hmem : (rotOf u)[0]'h0_pos ∈ (rc.adj[u]'hu_adj).toList := hperm.mem_iff.mp hmem_rot
        have hv_lt : (rotOf u)[0]'h0_pos < c.totalNodes := ((hadj.1 u hun).2 _ hmem).1
        have hadj_uv : c.adj u ((rotOf u)[0]'h0_pos) = true := by
          rw [hadj.2.1 u hun _ hv_lt, List.contains_eq_mem, decide_eq_true_eq]
          exact hmem
        exact ⟨(rotOf u)[0]'h0_pos, hv_lt, hadj_uv⟩
      dart_same_vertex_rep := hint_same_vertex_fn
      dart_edge_same_vertex_rep := hdart_edge_sv
      adj_rep_edge := hadj_rep_edge_fn
      adj_rep_distinct := by
        intro i j hi hj hadj_ij
        have hadj_v := hadj_rep_edge_fn i j hi hj hadj_ij
        cases h_eq : sameVertex T (repFn i) (repFn j) darts.length with
        | false => rfl
        | true =>
          have hself : areAdjacentVertices T (repFn i) (repFn i) darts.length = true := by
            have h_refl := sameVertex_refl T darts.length (repFn i)
            rw [areAdjacentVertices_congr T darts h_all h_len h_refl h_eq]
            exact hadj_v
          have hirr := areAdjacentVertices_irrefl T darts h_all h_len h_loopless (repFn i)
          rw [hirr] at hself
          exact absurd hself (by decide)
      int_distinct := fun u1 u2 hu1r hu1n hu2r hu2n hne =>
        hint_distinct_fn u1 hu1r hu1n u2 hu2r hu2n hne
      int_ring_distinct := by
        intro u x hur hun hx
        have hur_c : c.ringSize ≤ u := hur
        have hun_c : u < c.totalNodes := hun
        have hx_c : x < c.ringSize := hx
        cases h_eq : sameVertex T (repFn u) (repFn x) darts.length with
        | false => rfl
        | true =>
          exfalso
          have hx_adj : x < rc.adj.size := by rw [hhdr.2.2.2.2.2.2.2.2.2.2.2.1, hc_n]; omega
          let fans := ((rc.adj[x]'hx_adj).toList.drop 1).dropLast
          have hrf := fastConf_geom_ring_fans h hh x (hr_eq ▸ hx_c)
          have hfans_ne : fans ≠ [] := hrf.1
          have hfans_pos : 0 < fans.length :=
            Nat.pos_of_ne_zero (fun h0 => hfans_ne (List.eq_nil_of_length_eq_zero h0))
          obtain ⟨u0, hu0_def⟩ : ∃ u0 : Nat, u0 = fans[0]'hfans_pos := ⟨_, rfl⟩
          have hu0_sv := hfan_same_vertex x hx_c hx_adj 0 hfans_pos
          have hu0_r : c.ringSize ≤ u0 := by rw [hu0_def]; exact hu0_sv.1
          have hu0_n : u0 < c.totalNodes := by rw [hu0_def]; exact hu0_sv.2.1
          have hx_n : x < c.totalNodes := by omega
          have hx_rep : repFn x = T.edge.f (dartFn u0 x) := by
            dsimp only [repFn]
            rw [dif_pos hx_c, List.getElem?_eq_getElem hfans_pos, ← hu0_def]
            rfl
          have hu0_mem : u0 ∈ (rc.adj[x]'hx_adj).toList := by
            rw [hu0_def]
            exact List.mem_of_mem_drop (mem_of_mem_dropLast (List.getElem_mem hfans_pos))
          have hadj_x_u0 : c.adj x u0 = true := by
            rw [hadj.2.1 x hx_n u0 hu0_n, List.contains_eq_mem, decide_eq_true_eq]
            exact hu0_mem
          have hadj_u0_x : c.adj u0 x = true := by
            have hsym := (hadj.2.2.1 u0 hu0_n x hx_n).1
            change c.adj u0 x = c.adj x u0 at hsym
            rw [hsym]; exact hadj_x_u0
          have hsv_d1_u0 : sameVertex T (dartFn u0 x) (repFn u0) darts.length = true :=
            hint_same_vertex_fn u0 hu0_r hu0_n x hx_n hadj_u0_x
          have hsv_ed1_u : sameVertex T (T.edge.f (dartFn u0 x)) (repFn u) darts.length = true := by
            rw [← hx_rep, sameVertex_symm_of_complete T darts h_all h_len]; exact h_eq
          have hne_u0_u : u0 ≠ u := by
            intro heq; subst heq
            have hsv_u0_d1 : sameVertex T (repFn u0) (dartFn u0 x) darts.length = true := by
              rw [sameVertex_symm_of_complete T darts h_all h_len]; exact hsv_d1_u0
            have hbad := sameVertex_trans_of_complete T darts h_all h_len hsv_ed1_u hsv_u0_d1
            rw [sameVertex_symm_of_complete T darts h_all h_len] at hbad
            rw [h_loopless (dartFn u0 x)] at hbad
            exact Bool.false_ne_true hbad
          obtain ⟨hact0, hsv_rep0, hbit0⟩ := hint_active u0 hu0_r hu0_n
          obtain ⟨hact_u, hsv_rep_u, hbit_u⟩ := hint_active u hur_c hun_c
          have hne_f : getImgNat img (u0 + 1) ≠ getImgNat img (u + 1) :=
            hint_img_ne u0 hu0_r hu0_n u hur_c hun_c hne_u0_u
          have hadj_u0_u_rep : areAdjacentVertices T (repFn u0) (repFn u) darts.length = true :=
            areAdjacentVertices_of_dart T darts h_all h_len hsv_d1_u0 hsv_ed1_u
          have hadj_u0_u_cart : areAdjacentVertices T
              (cartDartOriented T deg refl d0 (getImgNat img (u0 + 1)))
              (cartDartOriented T deg refl d0 (getImgNat img (u + 1))) darts.length = true := by
            rw [← areAdjacentVertices_congr T darts h_all h_len hsv_rep0 hsv_rep_u]
            exact hadj_u0_u_rep
          have hpca := hcw.2.1 _ _ hact0 hact_u hne_f hadj_u0_u_cart
          have hpc := pureCartAdj_implies_c_adj hh hdeg5 hdeg11 hmin5 hm31 hlen hinit hspoke hindu
            hexact hbit0 hbit_u hpca
          dsimp only at hpc
          obtain ⟨_, _, _, hiv0_mem, hiv0_u, _⟩ := intVert_of_ge_ring hh hlen hu0_r hu0_n
          obtain ⟨_, _, _, hivu_mem, hivu_u, _⟩ := intVert_of_ge_ring hh hlen hur_c hun_c
          have h_all_spec := hinit_s.2.2.1
          have hln0 := (h_all_spec _ hiv0_mem).2.2.2
          have hln_u := (h_all_spec _ hivu_mem).2.2.2
          rw [hiv0_u] at hln0; rw [hivu_u] at hln_u
          have hln0' : getLaneNat invMap (getImgNat img (u0 + 1)) = u0 + 1 - (c.ringSize + 1) := hln0
          have hln_u' : getLaneNat invMap (getImgNat img (u + 1)) = u + 1 - (c.ringSize + 1) := hln_u
          have hadd_sub : ∀ r val : Nat, r ≤ val → r + (val + 1 - (r + 1)) = val := by
            intro r val hrv; omega
          have hu0_lane : c.ringSize + getLaneNat invMap (getImgNat img (u0 + 1)) = u0 := by
            rw [hln0']; exact hadd_sub c.ringSize u0 hu0_r
          have hu_lane : c.ringSize + getLaneNat invMap (getImgNat img (u + 1)) = u := by
            rw [hln_u']; exact hadd_sub c.ringSize u hur_c
          rw [hu0_lane, hu_lane] at hpc
          have hadj_u0_u : c.adj u0 u = true := hpc.1
          have hsv_d2_u0 : sameVertex T (dartFn u0 u) (repFn u0) darts.length = true :=
            hint_same_vertex_fn u0 hu0_r hu0_n u hun_c hadj_u0_u
          have hsv_ed2_u : sameVertex T (T.edge.f (dartFn u0 u)) (repFn u) darts.length = true := by
            rw [hint_edge_flip_fn u0 hu0_r hu0_n u hur_c hun_c hadj_u0_u]
            have hadj_u_u0 : c.adj u u0 = true := by
              have hsym := (hadj.2.2.1 u0 hu0_n u hun_c).1
              change c.adj u0 u = c.adj u u0 at hsym
              rw [← hsym]; exact hadj_u0_u
            exact hint_same_vertex_fn u hur_c hun_c u0 hu0_n hadj_u_u0
          have hd1_eq_d2 : dartFn u0 x = dartFn u0 u :=
            hcw.2.2 _ _ hact0 hact_u hne_f (dartFn u0 x) (dartFn u0 u)
              (sameVertex_trans_of_complete T darts h_all h_len hsv_d1_u0 hsv_rep0)
              (sameVertex_trans_of_complete T darts h_all h_len hsv_d2_u0 hsv_rep0)
              (sameVertex_trans_of_complete T darts h_all h_len hsv_ed1_u hsv_rep_u)
              (sameVertex_trans_of_complete T darts h_all h_len hsv_ed2_u hsv_rep_u)
          obtain ⟨hu0_adj, _, _, _, _, hdeg_u0, _, hperm_u0, _⟩ := hrot_facts u0 hu0_r hu0_n
          have hx_in_adj : x ∈ (rc.adj[u0]'hu0_adj).toList := by
            rw [hadj.2.1 u0 hu0_n x hx_n, List.contains_eq_mem, decide_eq_true_eq] at hadj_u0_x
            exact hadj_u0_x
          have hu_in_adj : u ∈ (rc.adj[u0]'hu0_adj).toList := by
            rw [hadj.2.1 u0 hu0_n u hun_c, List.contains_eq_mem, decide_eq_true_eq] at hadj_u0_u
            exact hadj_u0_u
          have hx_in_rot : x ∈ rotOf u0 := hperm_u0.mem_iff.mpr hx_in_adj
          have hu_in_rot : u ∈ rotOf u0 := hperm_u0.mem_iff.mpr hu_in_adj
          have hpx_lt : posInList x (rotOf u0) < nodeDegree T (baseDartOf u0) darts.length := by
            rw [hdeg_u0]; exact posInList_lt hx_in_rot
          have hpu_lt : posInList u (rotOf u0) < nodeDegree T (baseDartOf u0) darts.length := by
            rw [hdeg_u0]; exact posInList_lt hu_in_rot
          have hp_eq := perm_iter_nodePermOriented_inj_lt_deg T darts h_all h_len orient (baseDartOf u0)
            hpx_lt hpu_lt hd1_eq_d2
          have hxu := posInList_inj hx_in_rot hu_in_rot hp_eq
          have hne_xu : x ≠ u := by omega
          exact hne_xu hxu
      int_inj_neighbor := by
        intro u hur hun v1 v2 hv1 hv2 hadj1 hadj2 hne heq
        obtain ⟨hu_adj, _, _, _, _, hdeg_u, _, hperm_u, _⟩ := hrot_facts u hur hun
        have hv1_adj : v1 ∈ (rc.adj[u]'hu_adj).toList := by
          rw [hadj.2.1 u hun v1 hv1, List.contains_eq_mem, decide_eq_true_eq] at hadj1; exact hadj1
        have hv2_adj : v2 ∈ (rc.adj[u]'hu_adj).toList := by
          rw [hadj.2.1 u hun v2 hv2, List.contains_eq_mem, decide_eq_true_eq] at hadj2; exact hadj2
        have hv1_rot : v1 ∈ rotOf u := hperm_u.mem_iff.mpr hv1_adj
        have hv2_rot : v2 ∈ rotOf u := hperm_u.mem_iff.mpr hv2_adj
        have hp1_lt : posInList v1 (rotOf u) < nodeDegree T (baseDartOf u) darts.length := by
          rw [hdeg_u]; exact posInList_lt hv1_rot
        have hp2_lt : posInList v2 (rotOf u) < nodeDegree T (baseDartOf u) darts.length := by
          rw [hdeg_u]; exact posInList_lt hv2_rot
        have hp_eq := perm_iter_nodePermOriented_inj_lt_deg T darts h_all h_len orient (baseDartOf u)
          hp1_lt hp2_lt heq
        exact hne (posInList_inj hv1_rot hv2_rot hp_eq)
      int_degree_match := by
        intro u hur hun
        obtain ⟨hu_adj, _, _, _, _, hdeg_u, _, hperm_u, _⟩ := hrot_facts u hur hun
        have hnot : ¬ (u < c.ringSize) := Nat.not_lt_of_ge hur
        simp only [repFn, hnot, dite_false]
        rw [hdeg_u, hperm_u.length_eq]
        symm
        exact countP_range_eq_length_of_nodup c.totalNodes (fun w => c.adj u w)
          (rc.adj[u]'hu_adj).toList (hadj.1 u hun).1
          (fun w hw => ((hadj.1 u hun).2 w hw).1)
          (fun w hw => hadj.2.1 u hun w hw)
      int_edge_flip := fun u v hur hun hvr hvn hadj_uv =>
        hint_edge_flip_fn u hur hun v hvr hvn hadj_uv }
  exact ⟨h, hh, emb, hmatches_fn⟩

/-- Unavoidability of a configuration in `theUnavoidableSet` with an explicit cyclic
    `TriangulationEmbedding` and `MatchesConfCycle` into any complete planar triangulation `T`. -/
theorem unavoidability_appearsInTriangulation_matched
    (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_nodup : darts.Nodup) (h_all : ∀ d : T.Dart, d ∈ darts)
    (h_bridge : Math.Hypermap.isBridgeless T darts)
    (h_planar : T.isPlanar darts.length darts = true)
    (h_conn : T.numComponents darts.length darts = 1)
    (h_loopless : ∀ d : T.Dart, sameVertex T d (T.edge.f d) darts.length = false)
    (h_tri : ∀ d : T.Dart, d ∈ darts → faceDegree T d darts.length = 3)
    (h5_all : ∀ d : T.Dart, d ∈ darts → 5 ≤ nodeDegree T d darts.length)
    (h_cw : ∀ (refl : Bool) (d0 : T.Dart),
      5 ≤ nodeDegree T d0 darts.length →
      nodeDegree T d0 darts.length ≤ 11 →
      CartwheelEmbedded T darts.length refl d0) :
    ∃ (h : Nat) (hh : h < 633),
      ∃ (e : TriangulationEmbedding
        (configOfRConf (parsedRConfList[h]'(Math.Unavoidability.parsedRConfList_length ▸ hh))) T darts),
        MatchesConfCycle
          (parsedRConfList[h]'(Math.Unavoidability.parsedRConfList_length ▸ hh)) T darts e := by
  obtain ⟨d0, refl, hdeg5, hdeg11, hred⟩ :=
    exists_hasExactReducedAxle_of_complete_triangulation T darts h_nodup h_all
      h_bridge h_planar h_conn h_loopless h_tri h5_all
  exact triangulation_embedding_of_hasExactReducedAxle T darts h_all h_loopless h_tri h5_all
    refl d0 hdeg11 (h_cw refl d0 hdeg5 hdeg11) hred

/-- Phase 5 Unavoidability (`AppearsInTriangulation`): every complete planar bridgeless
    connected triangulation of minimum degree ≥ 5 whose small-degree cartwheels embed
    cleanly contains some unavoidable configuration `c ∈ theUnavoidableSet`. -/
theorem unavoidability_appearsInTriangulation
    (T : Hypermap) [DecidableEq T.Dart]
    (darts : List T.Dart) (h_nodup : darts.Nodup) (h_all : ∀ d : T.Dart, d ∈ darts)
    (h_bridge : Math.Hypermap.isBridgeless T darts)
    (h_planar : T.isPlanar darts.length darts = true)
    (h_conn : T.numComponents darts.length darts = 1)
    (h_loopless : ∀ d : T.Dart, sameVertex T d (T.edge.f d) darts.length = false)
    (h_tri : ∀ d : T.Dart, d ∈ darts → faceDegree T d darts.length = 3)
    (h5_all : ∀ d : T.Dart, d ∈ darts → 5 ≤ nodeDegree T d darts.length)
    (h_cw : ∀ (refl : Bool) (d0 : T.Dart),
      5 ≤ nodeDegree T d0 darts.length →
      nodeDegree T d0 darts.length ≤ 11 →
      CartwheelEmbedded T darts.length refl d0) :
    ∃ c ∈ theUnavoidableSet, AppearsInTriangulation c T darts := by
  obtain ⟨h, hh, e, _⟩ := unavoidability_appearsInTriangulation_matched T darts h_nodup h_all
    h_bridge h_planar h_conn h_loopless h_tri h5_all h_cw
  have hmem : theUnavoidableSet[h]'(by rw [theUnavoidableSet_size]; exact hh) ∈ theUnavoidableSet :=
    Array.getElem_mem _
  have heq := theUnavoidableSet_getElem h hh
  exact ⟨_, hmem, ⟨heq.symm ▸ e⟩⟩

/-- Dual Cubic Unavoidability (matched): on `H.dual` of any connected bridgeless cubic planar
    map `H` with `faceDegree ≥ 5` and faithful small-degree cartwheels on `H.dual`, some
    unavoidable configuration `h < 633` admits a `TriangulationEmbedding` and `MatchesConfCycle`. -/
theorem dual_unavoidability_appearsInTriangulation_matched
    (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_bridge : Math.Hypermap.isBridgeless H darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    (h_cubic : ∀ d : H.Dart, d ∈ darts → nodeDegree H d darts.length = 3)
    (h_face5 : ∀ d : H.Dart, d ∈ darts → 5 ≤ faceDegree H d darts.length)
    (h_cw : ∀ (refl : Bool) (d0 : H.Dart),
      5 ≤ nodeDegree H.dual d0 darts.length →
      nodeDegree H.dual d0 darts.length ≤ 11 →
      CartwheelEmbedded H.dual darts.length refl d0) :
    ∃ (h : Nat) (hh : h < 633),
      ∃ (e : TriangulationEmbedding
        (configOfRConf (parsedRConfList[h]'(Math.Unavoidability.parsedRConfList_length ▸ hh))) H.dual darts),
        MatchesConfCycle
          (parsedRConfList[h]'(Math.Unavoidability.parsedRConfList_length ▸ hh)) H.dual darts e := by
  have h_loopless : ∀ d : H.Dart, sameVertex H.dual d (H.dual.edge.f d) darts.length = false :=
    dual_sameVertex_edge_eq_false_of_isBridgeless H darts h_all (Nat.le_refl _) (Nat.le_refl _) h_bridge
  have h_tri : ∀ d : H.Dart, d ∈ darts → faceDegree H.dual d darts.length = 3 := by
    intro d hd
    rw [faceDegree_dual_eq_nodeDegree_of_complete H darts h_all (Nat.le_refl _) d]
    exact h_cubic d hd
  have h5_all : ∀ d : H.Dart, d ∈ darts → 5 ≤ nodeDegree H.dual d darts.length := by
    intro d hd
    rw [nodeDegree_dual_eq_faceDegree_of_complete H darts h_all (Nat.le_refl _) d]
    exact h_face5 d hd
  obtain ⟨d0, refl, hdeg5, hdeg11, hred⟩ :=
    dual_exists_hasExactReducedAxle_of_cubic H darts h_nodup h_all (Nat.le_refl _) h_bridge
      h_planar h_conn h_cubic h_face5
  exact triangulation_embedding_of_hasExactReducedAxle H.dual darts h_all h_loopless h_tri h5_all
    refl d0 hdeg11 (h_cw refl d0 hdeg5 hdeg11) hred

/-- Dual Cubic Unavoidability (`AppearsInTriangulation` on `H.dual`): every connected bridgeless
    cubic planar map `H` of girth ≥ 5 whose dual cartwheels embed contains some `c ∈ theUnavoidableSet`. -/
theorem dual_unavoidability_appearsInTriangulation
    (H : Hypermap) [DecidableEq H.Dart]
    (darts : List H.Dart) (h_nodup : darts.Nodup) (h_all : ∀ d : H.Dart, d ∈ darts)
    (h_bridge : Math.Hypermap.isBridgeless H darts)
    (h_planar : H.isPlanar darts.length darts = true)
    (h_conn : H.numComponents darts.length darts = 1)
    (h_cubic : ∀ d : H.Dart, d ∈ darts → nodeDegree H d darts.length = 3)
    (h_face5 : ∀ d : H.Dart, d ∈ darts → 5 ≤ faceDegree H d darts.length)
    (h_cw : ∀ (refl : Bool) (d0 : H.Dart),
      5 ≤ nodeDegree H.dual d0 darts.length →
      nodeDegree H.dual d0 darts.length ≤ 11 →
      CartwheelEmbedded H.dual darts.length refl d0) :
    ∃ c ∈ theUnavoidableSet, AppearsInTriangulation c H.dual darts := by
  obtain ⟨h, hh, e, _⟩ := dual_unavoidability_appearsInTriangulation_matched H darts h_nodup h_all
    h_bridge h_planar h_conn h_cubic h_face5 h_cw
  have hmem : theUnavoidableSet[h]'(by rw [theUnavoidableSet_size]; exact hh) ∈ theUnavoidableSet :=
    Array.getElem_mem _
  have heq := theUnavoidableSet_getElem h hh
  exact ⟨_, hmem, ⟨heq.symm ▸ e⟩⟩

end AppearsInTriangulation

end Math.Unavoidability
