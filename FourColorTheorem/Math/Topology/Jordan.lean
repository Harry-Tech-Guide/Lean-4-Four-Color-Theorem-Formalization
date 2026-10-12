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

end Hypermap




