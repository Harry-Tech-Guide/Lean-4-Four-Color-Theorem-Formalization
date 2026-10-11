import FourColorTheorem.Math.Hypermap
import FourColorTheorem.Math.Planarity

namespace Hypermap

variable (H : Hypermap)

/-- A single step in the hypermap: along a node cycle (either direction),
    across an edge (an involution, so self-inverse), or along a face cycle (either direction).
    Steps are symmetric, so walk-connectivity is an equivalence relation. -/
inductive Step (d d' : H.Dart) : Prop
  | node : d' = H.node.f d → Step d d'
  | nodeInv : d' = H.node.inv d → Step d d'
  | edge : d' = H.edge.f d → Step d d'
  | face : d' = H.face.f d → Step d d'
  | faceInv : d' = H.face.inv d → Step d d'

/-- A Walk is a sequence of darts connected by valid topological steps. -/
inductive Walk : H.Dart → H.Dart → Type
  | refl (d : H.Dart) : Walk d d
  | step {d1 d2 d3 : H.Dart} : Step H d1 d2 → Walk d2 d3 → Walk d1 d3

/-- A Cycle is a walk that starts and ends at the same dart, with at least one step. -/
def IsCycle {d : H.Dart} (w : Walk H d d) : Prop :=
  match w with
  | Walk.refl _ => False
  | Walk.step _ _ => True

/-- The list of darts visited by a walk (both endpoints included). -/
def Walk.toList {d1 d2 : H.Dart} (w : Walk H d1 d2) : List H.Dart :=
  match w with
  | Walk.refl d => [d]
  | Walk.step _ w' => d1 :: Walk.toList w'

def Walk.isSimple {d1 d2 : H.Dart} (w : Walk H d1 d2) : Prop :=
  (Walk.toList H w).Nodup

/-- Extend a walk by one step at its end. -/
def Walk.snoc : {d1 d2 d3 : H.Dart} → Walk H d1 d2 → Step H d2 d3 → Walk H d1 d3
  | _, _, _, Walk.refl _, s => Walk.step s (Walk.refl _)
  | _, _, _, Walk.step s' w, s => Walk.step s' (Walk.snoc w s)

theorem Walk.toList_snoc {d1 d2 d3 : H.Dart} (w : Walk H d1 d2) (s : Step H d2 d3) :
    Walk.toList H (Walk.snoc H w s) = Walk.toList H w ++ [d3] := by
  induction w with
  | refl d => simp [Walk.snoc, Walk.toList]
  | step _ w ih => simp [Walk.snoc, Walk.toList, ih]

/-- Every node step can be undone by a step. -/
theorem Step.node_back (d : H.Dart) : Step H (H.node.f d) d :=
  Step.nodeInv (H.node.left_inv d).symm

/-- Every edge step can be undone by a step (edge is an involution). -/
theorem Step.edge_back (d : H.Dart) : Step H (H.edge.f d) d :=
  Step.edge (H.edge_involution d).symm

end Hypermap
