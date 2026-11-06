import Spec
import ConditionalBridge
import FourColorTheorem.Math.MainTheorem

/-!
# Conditional Four Color Theorem (sorry-free, but NOT the full theorem)

This module proves `four_color_theorem_conditional`: the Four Color Theorem *assuming*
`Spec.RSSTStandardizationBridge`.

> **Warning.** `Spec.ValidRSSTCertificateSuite` is satisfiable by trivial data, so the bridge is
> equivalent to "no minimal counterexample exists" (see `SanityChecks.bridge_iff_no_mc`). This
> theorem is therefore *not* an unconditional proof; the hypothesis-free statement lives in
> `Challenge.lean` / `Solution.lean` and is still open.

What *is* established here (kernel-checked, standard axioms only): the 633 RSST configurations and
the 5 cartwheel discharging trees pass in-kernel computational checks, and well-founded descent
reduces the theorem to the absence of a minimal counterexample.
-/

namespace SolutionInternal

/-- Lossless conversion from `Spec.Perm` to the internal `_root_.Perm`. -/
def toCorePerm {D : Type} (p : Spec.Perm D) : _root_.Perm D where
  f := p.f
  inv := p.inv
  left_inv := p.left_inv
  right_inv := p.right_inv

/-- Lossless conversion from `Spec.Hypermap` to the internal `_root_.Hypermap`
    (with `(toCore H).Dart = H.Dart` definitionally). -/
def toCore (H : Spec.Hypermap) : _root_.Hypermap where
  Dart := H.Dart
  edge := toCorePerm H.edge
  node := toCorePerm H.node
  face := toCorePerm H.face
  edge_involution := H.edge_involution
  edge_node_face_id := H.edge_node_face_id

/-- Interior size of canonical unavoidable configuration `idx < 633`. -/
def canonicalInteriorSize (idx : Nat) : Nat :=
  if h : idx < 633 then
    (Math.theUnavoidableSet[idx]'(by rw [Math.unavoidable_size_eq]; exact h)).interiorSize
  else
    0

/-- The in-kernel RSST certificate suite (all 633 unavoidable configurations, all 138 D/C
    batch reducibility certificates, all 28 cartwheel discharging verification modules, and
    the 32-rule skew-symmetric `rsstShift` conservation theorem) satisfies
    `Spec.ValidRSSTCertificateSuite`. -/
theorem internal_rsst_suite_valid :
    Spec.ValidRSSTCertificateSuite
      Math.theUnavoidableSet.size
      canonicalInteriorSize
      Math.KernelReducer.verifyIdxD
      Math.KernelReducer.verifyIdxC
      (Math.Discharging.DischargingTreesVerified Math.theUnavoidableSet.toList)
      (fun H _ u v => Math.Discharging.rsstShift (toCore H) 1000 u v) := by
  refine ⟨Math.unavoidable_size_eq, ?_, ?_, Math.Discharging.discharging_trees_verified, ?_⟩
  · intro idx h_lt
    dsimp [canonicalInteriorSize]
    rw [dif_pos h_lt]
    have h_mem :
        Math.theUnavoidableSet[idx]'(by rw [Math.unavoidable_size_eq]; exact h_lt) ∈
          Math.theUnavoidableSet :=
      Array.getElem_mem _
    exact Math.unavoidable_interior_ge_4 _ h_mem
  · intro idx h_lt
    rcases Math.MasterCertificate.master_suite_certifies_idx idx h_lt with ⟨_, hD⟩ | ⟨_, hC⟩
    · exact Or.inl hD
    · exact Or.inr hC
  · intro H dec u v
    exact @Math.Discharging.rsstShift_conservation (toCore H) dec 1000 u v

/-- Predicate asserting that a counterexample of dart length `n` exists. -/
def IsSpecCounterexampleOfSize (n : Nat) : Prop :=
  ∃ (H : Spec.Hypermap) (_ : DecidableEq H.Dart) (darts : List H.Dart),
    Spec.IsCompleteDarts H darts ∧
    darts.length = n ∧
    Spec.IsPlanar H darts ∧
    Spec.Hypermap.isBridgeless H darts ∧
    (Spec.MapColoring H → False)

/-- Well-ordering descent: if any planar bridgeless counterexample exists, a minimal one exists. -/
theorem minimal_counterexample_exists (H : Spec.Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_complete : Spec.IsCompleteDarts H darts)
    (h_planar : Spec.IsPlanar H darts)
    (h_bridgeless : Spec.Hypermap.isBridgeless H darts)
    (h_not_colorable : Spec.MapColoring H → False) :
    ∃ (H' : Spec.Hypermap) (_ : DecidableEq H'.Dart) (darts' : List H'.Dart),
      Spec.MinimalCounterexample H' darts' := by
  have hEx : IsSpecCounterexampleOfSize darts.length :=
    ⟨H, inferInstance, darts, h_complete, rfl, h_planar, h_bridgeless, h_not_colorable⟩
  have ⟨n, _, hPn, hmin⟩ := Math.find_least IsSpecCounterexampleOfSize darts.length hEx
  rcases hPn with ⟨H0, dec0, darts0, hcomp0, hlen, hplan, hbridge, hnotcol⟩
  refine ⟨H0, dec0, darts0, ⟨hcomp0, hplan, hbridge, hnotcol, ?_⟩⟩
  intro H' dec' darts' hcomp' hlt hplan' hbridge'
  by_cases hcol' : Nonempty (Spec.MapColoring H')
  · exact hcol'
  · have hcolFalse : Spec.MapColoring H' → False := fun c => hcol' ⟨c⟩
    have hEx' : IsSpecCounterexampleOfSize darts'.length :=
      ⟨H', dec', darts', hcomp', rfl, hplan', hbridge', hcolFalse⟩
    rw [← hlen] at hmin
    exact False.elim (hmin darts'.length hlt hEx')

end SolutionInternal

/-- The Four Color Theorem, conditional on the (self-equivalent) RSST bridge h_rsst. -/
theorem four_color_theorem_conditional (H : Spec.Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_complete : Spec.IsCompleteDarts H darts)
    (h_planar : Spec.IsPlanar H darts)
    (h_bridgeless : Spec.Hypermap.isBridgeless H darts)
    (h_rsst : Spec.RSSTStandardizationBridge) :
    Nonempty (Spec.MapColoring H) := by
  by_cases h_colorable : Nonempty (Spec.MapColoring H)
  · exact h_colorable
  · have h_not : Spec.MapColoring H → False := fun c => h_colorable ⟨c⟩
    rcases SolutionInternal.minimal_counterexample_exists H darts h_complete h_planar h_bridgeless h_not with
      ⟨H', dec', darts', mc⟩
    exact False.elim
      (@h_rsst
        Math.theUnavoidableSet.size
        SolutionInternal.canonicalInteriorSize
        Math.KernelReducer.verifyIdxD
        Math.KernelReducer.verifyIdxC
        (Math.Discharging.DischargingTreesVerified Math.theUnavoidableSet.toList)
        (fun H0 dec u v => @Math.Discharging.rsstShift (SolutionInternal.toCore H0) dec 1000 u v)
        SolutionInternal.internal_rsst_suite_valid
        H' dec' darts' mc)

/--
info: 'four_color_theorem_conditional' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms four_color_theorem_conditional
