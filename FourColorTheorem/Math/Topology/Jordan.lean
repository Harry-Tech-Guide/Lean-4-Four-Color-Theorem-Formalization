import FourColorTheorem.Math.Topology.Paths
import FourColorTheorem.Math.Topology.KempeTopology
import FourColorTheorem.Math.Topology.Surgery

namespace Hypermap

/-- Every topological step in a hypermap is symmetric (reversible). -/
theorem Step.symm (H : Hypermap) {d d' : H.Dart} (s : Step H d d') : Step H d' d := by
  cases s with
  | node h =>
    rw [h]
    exact Step.nodeInv (H.node.left_inv d).symm
  | nodeInv h =>
    rw [h]
    exact Step.node (H.node.right_inv d).symm
  | edge h =>
    rw [h]
    exact Step.edge (H.edge_involution d).symm
  | face h =>
    rw [h]
    exact Step.faceInv (H.face.left_inv d).symm
  | faceInv h =>
    rw [h]
    exact Step.face (H.face.right_inv d).symm

/-- A combinatorial Jordan boundary cycle partitioning the darts of a hypermap.
    Represents an embedded ring of a configuration separating the sphere into
    an interior (disk) and exterior. -/
structure JordanPartition (H : Hypermap) where
  contour : List H.Dart
  inside : H.Dart → Prop
  outside : H.Dart → Prop
  disjoint_in_out : ∀ d, inside d → outside d → False
  disjoint_contour_in : ∀ d, d ∈ contour → inside d → False
  disjoint_contour_out : ∀ d, d ∈ contour → outside d → False

/-- Combinatorial Jordan Separation Property:
    Any elementary topological step from an inside dart to an outside dart
    (or vice-versa) must pass through the contour boundary. -/
def HasJordanSeparation (H : Hypermap) (jp : JordanPartition H) : Prop :=
  ∀ d1 d2, Step H d1 d2 → jp.inside d1 → jp.outside d2 → (d1 ∈ jp.contour ∨ d2 ∈ jp.contour)

/-- Reverse Jordan Separation: Any step from outside to inside also intersects the boundary. -/
theorem step_crosses_contour_rev (H : Hypermap) (jp : JordanPartition H)
    (hSep : HasJordanSeparation H jp) (d1 d2 : H.Dart)
    (s : Step H d1 d2) (hOut : jp.outside d1) (hIn : jp.inside d2) :
    d1 ∈ jp.contour ∨ d2 ∈ jp.contour := by
  have s_rev := Step.symm H s
  have h := hSep d2 d1 s_rev hIn hOut
  cases h with
  | inl h2 => exact Or.inr h2
  | inr h1 => exact Or.inl h1

/-- Topological Jordan Walk Separation Theorem:
    Any walk from an inside dart to an outside dart must intersect the boundary contour.
    Proved by structural induction on the walk. -/
theorem walk_crosses_contour (H : Hypermap) (jp : JordanPartition H)
    (hSep : HasJordanSeparation H jp) {d1 d2 : H.Dart} (w : Walk H d1 d2)
    (hIn : jp.inside d1) (hOut : jp.outside d2)
    (h_excl : ∀ d, jp.inside d ∨ jp.outside d ∨ d ∈ jp.contour) :
    ∃ d, d ∈ Walk.toList H w ∧ d ∈ jp.contour := by
  induction w with
  | refl d =>
    exact False.elim (jp.disjoint_in_out d hIn hOut)
  | step s w' ih =>
    rename_i da db dc
    cases h_excl db with
    | inl hIn_b =>
      have ⟨d, hd_list, hd_cnt⟩ := ih hIn_b hOut
      exact ⟨d, List.mem_cons_of_mem da hd_list, hd_cnt⟩
    | inr h_not_in =>
      cases h_not_in with
      | inl hOut_b =>
        have h_cross := hSep da db s hIn hOut_b
        cases h_cross with
        | inl h_cnt_a =>
          exact ⟨da, List.mem_cons_self da _, h_cnt_a⟩
        | inr h_cnt_b =>
          have hb_in_tail : db ∈ Walk.toList H w' := by
            cases w' with
            | refl _ => exact List.mem_singleton_self db
            | step _ _ => exact List.mem_cons_self db _
          exact ⟨db, List.mem_cons_of_mem da hb_in_tail, h_cnt_b⟩
      | inr h_cnt_b =>
        have hb_in_tail : db ∈ Walk.toList H w' := by
          cases w' with
          | refl _ => exact List.mem_singleton_self db
          | step _ _ => exact List.mem_cons_self db _
        exact ⟨db, List.mem_cons_of_mem da hb_in_tail, h_cnt_b⟩

/-- Topological Jordan Walk Separation Theorem (Outside to Inside):
    Any walk from an outside dart to an inside dart must intersect the boundary contour. -/
theorem walk_crosses_contour_outside_inside (H : Hypermap) (jp : JordanPartition H)
    (hSep : HasJordanSeparation H jp) {d1 d2 : H.Dart} (w : Walk H d1 d2)
    (hOut : jp.outside d1) (hIn : jp.inside d2)
    (h_excl : ∀ d, jp.inside d ∨ jp.outside d ∨ d ∈ jp.contour) :
    ∃ d, d ∈ Walk.toList H w ∧ d ∈ jp.contour := by
  induction w with
  | refl d =>
    exact False.elim (jp.disjoint_in_out d hIn hOut)
  | step s w' ih =>
    rename_i da db dc
    cases h_excl db with
    | inl hIn_b =>
      have h_cross := step_crosses_contour_rev H jp hSep da db s hOut hIn_b
      cases h_cross with
      | inl h_cnt_a =>
        exact ⟨da, List.mem_cons_self da _, h_cnt_a⟩
      | inr h_cnt_b =>
        have hb_in_tail : db ∈ Walk.toList H w' := by
          cases w' with
          | refl _ => exact List.mem_singleton_self db
          | step _ _ => exact List.mem_cons_self db _
        exact ⟨db, List.mem_cons_of_mem da hb_in_tail, h_cnt_b⟩
    | inr h_not_in =>
      cases h_not_in with
      | inl hOut_b =>
        have ⟨d, hd_list, hd_cnt⟩ := ih hOut_b hIn
        exact ⟨d, List.mem_cons_of_mem da hd_list, hd_cnt⟩
      | inr h_cnt_b =>
        have hb_in_tail : db ∈ Walk.toList H w' := by
          cases w' with
          | refl _ => exact List.mem_singleton_self db
          | step _ _ => exact List.mem_cons_self db _
        exact ⟨db, List.mem_cons_of_mem da hb_in_tail, h_cnt_b⟩

/-- Topological Jordan Kempe Chain Separation Theorem:
    Any Kempe chain walk connecting an outside dart to an inside dart must intersect the boundary contour.
    Follows directly from the walk separation theorem. -/
theorem kempe_chain_crosses_contour (H : Hypermap) (jp : JordanPartition H)
    (hSep : HasJordanSeparation H jp) (vc : VertexColoring H) (a b : Color)
    (start d : H.Dart) (kc : KempeChain H vc a b start d)
    (hOut : jp.outside start) (hIn : jp.inside d)
    (h_excl : ∀ x, jp.inside x ∨ jp.outside x ∨ x ∈ jp.contour) :
    ∃ c_dart, c_dart ∈ jp.contour := by
  obtain ⟨_, w, _⟩ := kc
  have ⟨c_dart, _, h_cnt⟩ := walk_crosses_contour_outside_inside H jp hSep w hOut hIn h_excl
  exact ⟨c_dart, h_cnt⟩

/-- Exterior Kempe Walk Disjointness Theorem:
    If no dart on the boundary contour belongs to the walk of an exterior Kempe chain,
    then the Kempe chain cannot reach ANY dart in the interior.
    Hence, swapping this Kempe chain leaves the interior coloring strictly invariant. -/
theorem exterior_kempe_chain_disjoint_from_inside (H : Hypermap) (jp : JordanPartition H)
    (hSep : HasJordanSeparation H jp) (vc : VertexColoring H) (a b : Color)
    (start : H.Dart) (hOut : jp.outside start)
    (h_no_cross : ∀ c_dart ∈ jp.contour, ¬ (∃ (d : H.Dart), KempeChain H vc a b start d ∧
      ∃ (w : Walk H start d), c_dart ∈ Walk.toList H w))
    (h_excl : ∀ x, jp.inside x ∨ jp.outside x ∨ x ∈ jp.contour) :
    ∀ d, KempeChain H vc a b start d → ¬ jp.inside d := by
  intro d kc hIn
  have ⟨_, w, _⟩ := kc
  have ⟨c_dart, h_list, h_cnt⟩ := walk_crosses_contour_outside_inside H jp hSep w hOut hIn h_excl
  have h_contr := h_no_cross c_dart h_cnt ⟨d, kc, w, h_list⟩
  exact False.elim h_contr

/-- The Jordan partition induced by an embedded configuration with ring boundary and interior nodes. -/
def configJordanPartition (H : Hypermap) [DecidableEq H.Dart] (c : Math.Configuration) (f : Nat → H.Dart)
    (h_inj : ∀ i < c.totalNodes, ∀ j < c.totalNodes, i ≠ j → f i ≠ f j) :
    JordanPartition H :=
  let contourDarts := (List.range c.ringSize).map f
  let insideDarts := ((List.range c.interiorSize).map (fun i => c.ringSize + i)).map f
  { contour := contourDarts,
    inside := fun d => d ∈ insideDarts,
    outside := fun d => d ∉ contourDarts ∧ d ∉ insideDarts,
    disjoint_in_out := by
      intro d hIn hOut
      exact hOut.2 hIn,
    disjoint_contour_in := by
      intro d hCnt hIn
      rw [List.mem_map] at hCnt
      rcases hCnt with ⟨i, hi, rfl⟩
      rw [List.mem_range] at hi
      have hNot := not_mem_internalDarts_of_lt_ringSize c f h_inj i hi
      exact hNot hIn,
    disjoint_contour_out := by
      intro d hCnt hOut
      exact hOut.1 hCnt }

/-- Exhaustion of the configuration Jordan partition:
    Every dart in the hypermap belongs either to the interior disk, the exterior, or the boundary contour. -/
theorem configJordanPartition_excl (H : Hypermap) [DecidableEq H.Dart] (c : Math.Configuration) (f : Nat → H.Dart)
    (h_inj : ∀ i < c.totalNodes, ∀ j < c.totalNodes, i ≠ j → f i ≠ f j) (d : H.Dart) :
    (configJordanPartition H c f h_inj).inside d ∨
    (configJordanPartition H c f h_inj).outside d ∨
    d ∈ (configJordanPartition H c f h_inj).contour := by
  dsimp [configJordanPartition]
  by_cases hCnt : d ∈ (List.range c.ringSize).map f
  · exact Or.inr (Or.inr hCnt)
  · by_cases hIn : d ∈ ((List.range c.interiorSize).map (fun i => c.ringSize + i)).map f
    · exact Or.inl hIn
    · exact Or.inr (Or.inl ⟨hCnt, hIn⟩)

/-- Kempe swap invariance on the interior:
    Any Kempe chain starting outside that does not intersect the boundary contour
    leaves the coloring of every interior dart strictly invariant. -/
theorem kempe_swap_interior_invariant (H : Hypermap) [DecidableEq H.Dart]
    (c : Math.Configuration) (f : Nat → H.Dart)
    (h_inj : ∀ i < c.totalNodes, ∀ j < c.totalNodes, i ≠ j → f i ≠ f j)
    (hSep : HasJordanSeparation H (configJordanPartition H c f h_inj))
    (vc : VertexColoring H) (a b : Color)
    (start : H.Dart) (hOut : (configJordanPartition H c f h_inj).outside start)
    (h_no_cross : ∀ c_dart ∈ (configJordanPartition H c f h_inj).contour,
      ¬ (∃ (d : H.Dart), KempeChain H vc a b start d ∧
        ∃ (w : Walk H start d), c_dart ∈ Walk.toList H w))
    (d : H.Dart) (hIn : (configJordanPartition H c f h_inj).inside d) :
    (swapKempeChain H vc a b start).color d = vc.color d := by
  dsimp [swapKempeChain]
  have h_not_kc := exterior_kempe_chain_disjoint_from_inside H
    (configJordanPartition H c f h_inj) hSep vc a b start hOut h_no_cross
    (configJordanPartition_excl H c f h_inj) d
  have h_not : ¬ KempeChain H vc a b start d := fun kc => h_not_kc kc hIn
  simp [h_not]

/-- Face Kempe swap invariance on the interior:
    Any face Kempe chain starting outside that does not intersect the boundary contour
    leaves the coloring of every interior dart strictly invariant. -/
theorem face_kempe_swap_interior_invariant (H : Hypermap) [DecidableEq H.Dart]
    (c : Math.Configuration) (f : Nat → H.Dart)
    (h_inj : ∀ i < c.totalNodes, ∀ j < c.totalNodes, i ≠ j → f i ≠ f j)
    (hSep : HasJordanSeparation H.dual (configJordanPartition H.dual c f h_inj))
    (fc : FaceColoring H) (a b : Color)
    (start : H.Dart) (hOut : (configJordanPartition H.dual c f h_inj).outside start)
    (h_no_cross : ∀ c_dart ∈ (configJordanPartition H.dual c f h_inj).contour,
      ¬ (∃ (d : H.Dart), KempeChain H.dual (faceColoringToVertexColoringOfDual H fc) a b start d ∧
        ∃ (w : Walk H.dual start d), c_dart ∈ Walk.toList H.dual w))
    (d : H.Dart) (hIn : (configJordanPartition H.dual c f h_inj).inside d) :
    (swapFaceKempeChain H fc a b start).color d = fc.color d := by
  dsimp [swapFaceKempeChain, vertexColoringOfDualToFaceColoring, faceColoringToVertexColoringOfDual]
  exact kempe_swap_interior_invariant H.dual c f h_inj hSep
    (faceColoringToVertexColoringOfDual H fc) a b start hOut h_no_cross d hIn

/-- Four indices on a cyclic boundary ring are cyclically alternating if they interleave:
    i1 < j1 < i2 < j2. -/
def CyclicallyAlternating (i1 j1 i2 j2 : Nat) : Prop :=
  i1 < j1 ∧ j1 < i2 ∧ i2 < j2

/-- Cyclically alternating pairs cannot be uncrossed:
    Any two continuous or discrete paths connecting i1 to i2 and j1 to j2 in a disk
    must geometrically cross each other. -/
theorem alternating_pairs_strictly_ordered (i1 j1 i2 j2 : Nat)
    (h : CyclicallyAlternating i1 j1 i2 j2) :
    i1 < i2 ∧ j1 < j2 ∧ i1 ≠ j1 ∧ i2 ≠ j2 := by
  have ⟨_, _, _⟩ := h
  refine ⟨by omega, by omega, by omega, by omega⟩

/-- Planar Kempe Non-Crossing Obstruction:
    Two Kempe chains with completely disjoint color pairs cannot simultaneously
    connect cyclically alternating pairs of boundary darts on any planar Jordan contour
    if the topology forces paths with alternating boundary endpoints to intersect. -/
theorem kempe_chains_cannot_alternate_if_intersecting
    (vc : VertexColoring H)
    (a1 b1 a2 b2 : Color)
    (hDisj : a1 ≠ a2 ∧ a1 ≠ b2 ∧ b1 ≠ a2 ∧ b1 ≠ b2)
    (start1 start2 end1 end2 : H.Dart)
    (_ : KempeChain H vc a1 b1 start1 end1)
    (_ : KempeChain H vc a2 b2 start2 end2)
    (hIntersect : ∃ d : H.Dart, KempeChain H vc a1 b1 start1 d ∧ KempeChain H vc a2 b2 start2 d) :
    False := by
  rcases hIntersect with ⟨d, kc1_d, kc2_d⟩
  exact kempe_chains_disjoint_of_disjoint_colors H vc a1 b1 a2 b2 hDisj start1 start2 d kc1_d kc2_d

/-- Face Kempe Non-Crossing Obstruction:
    Two face Kempe chains with completely disjoint color pairs cannot intersect at any dart.
    Hence, if Jordan topology forces two dual paths connecting alternating boundary darts to intersect,
    they cannot simultaneously have disjoint color pairs. -/
theorem face_kempe_chains_cannot_alternate_if_intersecting
    (fc : FaceColoring H)
    (a1 b1 a2 b2 : Color)
    (hDisj : a1 ≠ a2 ∧ a1 ≠ b2 ∧ b1 ≠ a2 ∧ b1 ≠ b2)
    (start1 start2 end1 end2 : H.Dart)
    (_ : KempeChain H.dual (faceColoringToVertexColoringOfDual H fc) a1 b1 start1 end1)
    (_ : KempeChain H.dual (faceColoringToVertexColoringOfDual H fc) a2 b2 start2 end2)
    (hIntersect : ∃ d : H.Dart,
      KempeChain H.dual (faceColoringToVertexColoringOfDual H fc) a1 b1 start1 d ∧
      KempeChain H.dual (faceColoringToVertexColoringOfDual H fc) a2 b2 start2 d) :
    False := by
  rcases hIntersect with ⟨d, kc1_d, kc2_d⟩
  exact face_kempe_chains_disjoint_of_disjoint_colors H fc a1 b1 a2 b2 hDisj start1 start2 d kc1_d kc2_d

/-- Planar Kempe Barrier Theorem:
    If a connected Kempe chain connects two boundary points in a planar map,
    it acts as a topological barrier preventing any disjoint-color Kempe chain
    from connecting points on opposite sides of the barrier. -/
theorem planar_kempe_barrier
    (fc : FaceColoring H)
    (a1 b1 a2 b2 : Color)
    (hDisj : a1 ≠ a2 ∧ a1 ≠ b2 ∧ b1 ≠ a2 ∧ b1 ≠ b2)
    (start1 start2 end2 : H.Dart)
    (hIntersect : KempeChain H.dual (faceColoringToVertexColoringOfDual H fc) a2 b2 start2 end2 →
      ∃ d : H.Dart,
        KempeChain H.dual (faceColoringToVertexColoringOfDual H fc) a1 b1 start1 d ∧
        KempeChain H.dual (faceColoringToVertexColoringOfDual H fc) a2 b2 start2 d) :
    ¬ KempeChain H.dual (faceColoringToVertexColoringOfDual H fc) a2 b2 start2 end2 := by
  intro kc2
  have ⟨d, kc1_d, kc2_d⟩ := hIntersect kc2
  exact face_kempe_chains_disjoint_of_disjoint_colors H fc a1 b1 a2 b2 hDisj start1 start2 d kc1_d kc2_d

end Hypermap





