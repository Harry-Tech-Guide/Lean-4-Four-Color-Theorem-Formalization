import Spec
import FourColorTheorem.Math.MainTheorem

namespace SpecBridge

abbrev toMathPerm {D : Type} (p : Spec.Perm D) : Perm D :=
  { f := p.f
    inv := p.inv
    left_inv := p.left_inv
    right_inv := p.right_inv }

abbrev toMathHypermap (H : Spec.Hypermap) : Hypermap :=
  { Dart := H.Dart
    edge := toMathPerm H.edge
    node := toMathPerm H.node
    face := toMathPerm H.face
    edge_involution := H.edge_involution
    edge_node_face_id := H.edge_node_face_id }

def toSpecColor : Color → Spec.Color
  | .c0 => .c0
  | .c1 => .c1
  | .c2 => .c2
  | .c3 => .c3

theorem toSpecColor_inj {x y : Color} (h : toSpecColor x = toSpecColor y) : x = y := by
  cases x <;> cases y <;> simp [toSpecColor] at h ⊢

def toSpecMapColoring (H : Spec.Hypermap) (fc : Math.MapColoring (toMathHypermap H)) :
    Spec.MapColoring H :=
  { color := fun d => toSpecColor (fc.color d)
    face_invariant := fun d => congrArg toSpecColor (fc.face_invariant d)
    edge_proper := fun d heq => fc.edge_proper d (toSpecColor_inj heq) }

theorem getOrbitAux_eq {D : Type} [BEq D] (p : Spec.Perm D)
    (start current : D) (acc : List D) (fuel : Nat) :
    Spec.getOrbitAux p start current acc fuel =
      getOrbitAux (toMathPerm p) start current acc fuel := by
  induction fuel generalizing current acc with
  | zero => rfl
  | succ fuel' ih =>
    simp only [Spec.getOrbitAux, getOrbitAux, toMathPerm]
    split
    · rfl
    · exact ih _ _

theorem getOrbit_eq {D : Type} [BEq D] (p : Spec.Perm D) (fuel : Nat) (d : D) :
    Spec.getOrbit p fuel d = getOrbit (toMathPerm p) fuel d :=
  getOrbitAux_eq p d d [] fuel

theorem countOrbitsAux_eq {D : Type} [BEq D] (p : Spec.Perm D) (fuel steps : Nat) (l : List D) :
    Spec.countOrbitsAux p fuel steps l = countOrbitsAux (toMathPerm p) fuel steps l := by
  induction steps generalizing l with
  | zero => rfl
  | succ steps' ih =>
    cases l with
    | nil => rfl
    | cons d ds =>
      simp only [Spec.countOrbitsAux, countOrbitsAux, getOrbit_eq]
      rw [ih]

theorem countOrbits_eq {D : Type} [BEq D] (p : Spec.Perm D) (fuel : Nat) (l : List D) :
    Spec.countOrbits p fuel l = countOrbits (toMathPerm p) fuel l :=
  countOrbitsAux_eq p fuel l.length l

theorem getComponentAux_eq (H : Spec.Hypermap) [BEq H.Dart]
    (queue visited : List H.Dart) (fuel : Nat) :
    Spec.Hypermap.getComponentAux H queue visited fuel =
      Hypermap.getComponentAux (toMathHypermap H) queue visited fuel := by
  induction fuel generalizing queue visited with
  | zero => rfl
  | succ fuel' ih =>
    cases queue with
    | nil => rfl
    | cons d ds =>
      simp only [Spec.Hypermap.getComponentAux, Hypermap.getComponentAux, toMathHypermap, toMathPerm]
      split
      · exact ih ds visited
      · exact ih _ _

theorem getComponent_eq (H : Spec.Hypermap) [BEq H.Dart] (fuel : Nat) (d : H.Dart) :
    Spec.Hypermap.getComponent H fuel d = Hypermap.getComponent (toMathHypermap H) fuel d :=
  getComponentAux_eq H [d] [] (5 * fuel + 1)

theorem countComponentsAux_eq (H : Spec.Hypermap) [BEq H.Dart]
    (fuel steps : Nat) (l : List H.Dart) :
    Spec.Hypermap.countComponentsAux H fuel steps l =
      Hypermap.countComponentsAux (toMathHypermap H) fuel steps l := by
  induction steps generalizing l with
  | zero => rfl
  | succ steps' ih =>
    cases l with
    | nil => rfl
    | cons d ds =>
      simp only [Spec.Hypermap.countComponentsAux, Hypermap.countComponentsAux, getComponent_eq]
      rw [ih]

theorem countComponents_eq (H : Spec.Hypermap) [BEq H.Dart] (fuel : Nat) (l : List H.Dart) :
    Spec.Hypermap.countComponents H fuel l = Hypermap.countComponents (toMathHypermap H) fuel l :=
  countComponentsAux_eq H fuel l.length l

theorem isPlanar_eq (H : Spec.Hypermap) [BEq H.Dart] (fuel : Nat) (darts : List H.Dart) :
    Spec.Hypermap.isPlanar H fuel darts = Hypermap.isPlanar (toMathHypermap H) fuel darts := by
  simp only [Spec.Hypermap.isPlanar, Hypermap.isPlanar,
    countOrbits_eq, countComponents_eq, toMathHypermap]

theorem isCompleteDarts_toMath (H : Spec.Hypermap) (darts : List H.Dart)
    (h : Spec.IsCompleteDarts H darts) :
    Math.IsCompleteDarts (toMathHypermap H) darts :=
  h

theorem isPlanar_toMath (H : Spec.Hypermap) [BEq H.Dart] (darts : List H.Dart)
    (h : Spec.IsPlanar H darts) :
    Math.IsPlanar (toMathHypermap H) darts := by
  simpa [Spec.IsPlanar, Math.IsPlanar, isPlanar_eq] using h

theorem isBridgeless_toMath (H : Spec.Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h : Spec.Hypermap.isBridgeless H darts) :
    Math.Hypermap.isBridgeless (toMathHypermap H) darts := by
  intro d hd
  have hspec := h d hd
  simpa [Spec.Hypermap.isBridge, Spec.Hypermap.sameFace,
    Math.Hypermap.isBridge, Math.Hypermap.sameFace,
    getOrbit_eq, toMathHypermap, toMathPerm] using hspec

/-- Unconditional Four Color Theorem at the exact `Spec` interface. -/
theorem four_color_theorem_spec (H : Spec.Hypermap) [DecidableEq H.Dart] (darts : List H.Dart)
    (h_complete : Spec.IsCompleteDarts H darts)
    (h_planar : Spec.IsPlanar H darts)
    (h_bridgeless : Spec.Hypermap.isBridgeless H darts) :
    Nonempty (Spec.MapColoring H) := by
  obtain ⟨fc⟩ := Math.four_color_theorem (toMathHypermap H) darts
    (isCompleteDarts_toMath H darts h_complete)
    (isPlanar_toMath H darts h_planar)
    (isBridgeless_toMath H darts h_bridgeless)
  exact ⟨toSpecMapColoring H fc⟩

end SpecBridge
