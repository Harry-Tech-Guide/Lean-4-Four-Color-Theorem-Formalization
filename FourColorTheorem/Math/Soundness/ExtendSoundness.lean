import FourColorTheorem.Math.Reducibility
import FourColorTheorem.Math.Coloring
import FourColorTheorem.Math.FastReducer

namespace Math
namespace Soundness

open FastReducer

/-- Conversion from Nat (0..3) to Color. -/
def colorOfNat : Nat → Color
  | 0 => Color.c0
  | 1 => Color.c1
  | 2 => Color.c2
  | _ => Color.c3

@[simp] theorem colorOfNat_toNat (c : Color) : colorOfNat c.toNat = c := by
  cases c <;> rfl

theorem toNat_colorOfNat {n : Nat} (h : n < 4) : (colorOfNat n).toNat = n := by
  cases n with
  | zero => rfl
  | succ n =>
    cases n with
    | zero => rfl
    | succ n =>
      cases n with
      | zero => rfl
      | succ n =>
        cases n with
        | zero => rfl
        | succ n => omega

theorem colorOfNat_inj {n m : Nat} (hn : n < 4) (hm : m < 4) (h : colorOfNat n = colorOfNat m) : n = m := by
  have h' := congrArg Color.toNat h
  rwa [toNat_colorOfNat hn, toNat_colorOfNat hm] at h'

/-- Read color at index `i`, defaulting to 0. -/
def getCol (col : Array Nat) (i : Nat) : Nat := col.getD i 0

theorem size_set! (col : Array Nat) (v c : Nat) :
    (col.set! v c).size = col.size := by
  dsimp [Array.set!, Array.setD]
  split
  · exact Array.size_set col ⟨v, by assumption⟩ c
  · rfl

theorem getCol_set_eq (col : Array Nat) (v c : Nat) (hv : v < col.size) :
    getCol (col.set! v c) v = c := by
  dsimp [getCol, Array.getD, Array.set!, Array.setD]
  rw [dif_pos hv]
  have h_sz : v < (col.set ⟨v, hv⟩ c).size := by
    rw [Array.size_set]; exact hv
  rw [dif_pos h_sz]
  simp

theorem getCol_set_ne (col : Array Nat) (v c i : Nat) (hv : v < col.size) (hne : i ≠ v) :
    getCol (col.set! v c) i = getCol col i := by
  dsimp [getCol, Array.getD, Array.set!, Array.setD]
  rw [dif_pos hv]
  by_cases hi : i < col.size
  · have hi' : i < (col.set ⟨v, hv⟩ c).size := by
      rw [Array.size_set]; exact hi
    rw [dif_pos hi, dif_pos hi']
    rw [Array.getElem_set]
    split
    · rename_i h_eq
      exact False.elim (hne h_eq.symm)
    · rfl
  · have hi' : ¬ (i < (col.set ⟨v, hv⟩ c).size) := by
      rw [Array.size_set]; exact hi
    rw [dif_neg hi, dif_neg hi']

theorem colorFree_imp (nbrs : Array Nat) (col : Array Nat) (c : Nat)
    (hFree : colorFree nbrs col c = true) :
    ∀ x ∈ nbrs.data, getCol col x ≠ c := by
  intro x hx
  dsimp [colorFree] at hFree
  have h_all := List.all_eq_true.mp hFree x hx
  intro heq
  rw [getCol] at heq
  rw [heq] at h_all
  simp at h_all

theorem extend_step_cases (earlier : Array (Array Nat)) (n v : Nat) (col : Array Nat)
    (hv : v < n) (h_ok : (extend earlier n v col).1 = true) :
    ∃ c : Nat, c < 4 ∧ colorFree (earlier.getD v #[]) col c = true ∧
      (extend earlier n (v + 1) (col.set! v c)).1 = true ∧
      (extend earlier n v col).2 = (extend earlier n (v + 1) (col.set! v c)).2 := by
  have h_ext : extend earlier n v col =
    let nbrs := earlier.getD v #[]
    let res0 := if colorFree nbrs col 0 then extend earlier n (v + 1) (col.set! v 0) else (false, col)
    if res0.1 then res0 else
    let res1 := if colorFree nbrs col 1 then extend earlier n (v + 1) (col.set! v 1) else (false, col)
    if res1.1 then res1 else
    let res2 := if colorFree nbrs col 2 then extend earlier n (v + 1) (col.set! v 2) else (false, col)
    if res2.1 then res2 else
    let res3 := if colorFree nbrs col 3 then extend earlier n (v + 1) (col.set! v 3) else (false, col)
    if res3.1 then res3 else
    (false, col) := by
    conv => lhs; rw [extend]; rw [dif_pos hv]
  let nbrs := earlier.getD v #[]
  let r0 := if colorFree nbrs col 0 then extend earlier n (v + 1) (col.set! v 0) else (false, col)
  let r1 := if colorFree nbrs col 1 then extend earlier n (v + 1) (col.set! v 1) else (false, col)
  let r2 := if colorFree nbrs col 2 then extend earlier n (v + 1) (col.set! v 2) else (false, col)
  let r3 := if colorFree nbrs col 3 then extend earlier n (v + 1) (col.set! v 3) else (false, col)
  have h_res : extend earlier n v col =
    (if r0.1 then r0 else if r1.1 then r1 else if r2.1 then r2 else if r3.1 then r3 else (false, col)) := by
    rw [h_ext]
  by_cases hr0 : r0.1 = true
  · have h_cf0 : colorFree nbrs col 0 = true := by
      cases hc : colorFree nbrs col 0 with
      | true => rfl
      | false =>
        have : r0 = (false, col) := by dsimp [r0]; rw [hc]; rfl
        rw [this] at hr0; contradiction
    have h_eq0 : r0 = extend earlier n (v + 1) (col.set! v 0) := by
      dsimp [r0]; rw [h_cf0]; rfl
    have h_final : extend earlier n v col = r0 := by
      rw [h_res]; rw [if_pos hr0]
    refine ⟨0, by omega, h_cf0, by rw [← h_eq0]; exact hr0, ?_⟩
    rw [h_final, h_eq0]
  · have hr0_f : r0.1 = false := by cases h : r0.1 with | true => contradiction | false => rfl
    by_cases hr1 : r1.1 = true
    · have h_cf1 : colorFree nbrs col 1 = true := by
        cases hc : colorFree nbrs col 1 with
        | true => rfl
        | false =>
          have : r1 = (false, col) := by dsimp [r1]; rw [hc]; rfl
          rw [this] at hr1; contradiction
      have h_eq1 : r1 = extend earlier n (v + 1) (col.set! v 1) := by
        dsimp [r1]; rw [h_cf1]; rfl
      have h_final : extend earlier n v col = r1 := by
        rw [h_res]; rw [if_neg hr0, if_pos hr1]
      refine ⟨1, by omega, h_cf1, by rw [← h_eq1]; exact hr1, ?_⟩
      rw [h_final, h_eq1]
    · have hr1_f : r1.1 = false := by cases h : r1.1 with | true => contradiction | false => rfl
      by_cases hr2 : r2.1 = true
      · have h_cf2 : colorFree nbrs col 2 = true := by
          cases hc : colorFree nbrs col 2 with
          | true => rfl
          | false =>
            have : r2 = (false, col) := by dsimp [r2]; rw [hc]; rfl
            rw [this] at hr2; contradiction
        have h_eq2 : r2 = extend earlier n (v + 1) (col.set! v 2) := by
          dsimp [r2]; rw [h_cf2]; rfl
        have h_final : extend earlier n v col = r2 := by
          rw [h_res]; rw [if_neg hr0, if_neg hr1, if_pos hr2]
        refine ⟨2, by omega, h_cf2, by rw [← h_eq2]; exact hr2, ?_⟩
        rw [h_final, h_eq2]
      · have hr2_f : r2.1 = false := by cases h : r2.1 with | true => contradiction | false => rfl
        by_cases hr3 : r3.1 = true
        · have h_cf3 : colorFree nbrs col 3 = true := by
            cases hc : colorFree nbrs col 3 with
            | true => rfl
            | false =>
              have : r3 = (false, col) := by dsimp [r3]; rw [hc]; rfl
              rw [this] at hr3; contradiction
          have h_eq3 : r3 = extend earlier n (v + 1) (col.set! v 3) := by
            dsimp [r3]; rw [h_cf3]; rfl
          have h_final : extend earlier n v col = r3 := by
            rw [h_res]; rw [if_neg hr0, if_neg hr1, if_neg hr2, if_pos hr3]
          refine ⟨3, by omega, h_cf3, by rw [← h_eq3]; exact hr3, ?_⟩
          rw [h_final, h_eq3]
        · have hr3_f : r3.1 = false := by cases h : r3.1 with | true => contradiction | false => rfl
          have h_final : extend earlier n v col = (false, col) := by
            rw [h_res]; rw [if_neg hr0, if_neg hr1, if_neg hr2, if_neg hr3]
          rw [h_final] at h_ok
          dsimp at h_ok
          contradiction

theorem extend_sound_ind (earlier : Array (Array Nat)) (n : Nat) (k : Nat) :
    ∀ (v : Nat) (col : Array Nat),
      n - v ≤ k →
      col.size ≥ n →
      (∀ i < v, getCol col i < 4) →
      (∀ i < v, ∀ u ∈ (earlier.getD i #[]).data, u < i → getCol col u ≠ getCol col i) →
      (extend earlier n v col).1 = true →
      let col' := (extend earlier n v col).2
      (∀ i < v, getCol col' i = getCol col i) ∧
      (∀ i < n, getCol col' i < 4) ∧
      (∀ i < n, ∀ u ∈ (earlier.getD i #[]).data, u < i → getCol col' u ≠ getCol col' i) := by
  induction k with
  | zero =>
    intro v col h_le h_sz h_lt4 h_adj h_ok
    have h_v : v ≥ n := by omega
    have he : extend earlier n v col = (true, col) := by
      rw [extend]
      have : ¬ (v < n) := by omega
      rw [dif_neg this]
    have h_col' : (extend earlier n v col).2 = col := by rw [he]
    dsimp
    rw [h_col']
    refine ⟨fun _ _ => rfl, ?_, ?_⟩
    · intro i hi
      exact h_lt4 i (by omega)
    · intro i hi u hu h_u_lt
      exact h_adj i (by omega) u hu h_u_lt
  | succ k ih =>
    intro v col h_le h_sz h_lt4 h_adj h_ok
    by_cases hv : v < n
    · rcases extend_step_cases earlier n v col hv h_ok with ⟨c, hc_lt, h_cf, h_ok_step, h_res2⟩
      let col1 := col.set! v c
      have h_sz1 : col1.size ≥ n := by
        rw [size_set!]; exact h_sz
      have hv_sz : v < col.size := by omega
      have h_lt4_1 : ∀ i < v + 1, getCol col1 i < 4 := by
        intro i hi
        by_cases h_iv : i = v
        · rw [h_iv]
          rw [getCol_set_eq col v c hv_sz]
          exact hc_lt
        · have : i < v := by omega
          rw [getCol_set_ne col v c i hv_sz h_iv]
          exact h_lt4 i this
      have h_adj_1 : ∀ i < v + 1, ∀ u ∈ (earlier.getD i #[]).data, u < i → getCol col1 u ≠ getCol col1 i := by
        intro i hi u hu h_u_lt
        by_cases h_iv : i = v
        · rw [h_iv]
          have h_u_ne : u ≠ v := by omega
          have hu_v : u ∈ (earlier.getD v #[]).data := by rw [← h_iv]; exact hu
          rw [getCol_set_eq col v c hv_sz]
          rw [getCol_set_ne col v c u hv_sz h_u_ne]
          exact colorFree_imp (earlier.getD v #[]) col c h_cf u hu_v
        · have hi_lt : i < v := by omega
          have hu_lt : u < v := by omega
          have h_i_ne : i ≠ v := by omega
          have h_u_ne : u ≠ v := by omega
          rw [getCol_set_ne col v c i hv_sz h_i_ne]
          rw [getCol_set_ne col v c u hv_sz h_u_ne]
          exact h_adj i hi_lt u hu h_u_lt
      have h_le1 : n - (v + 1) ≤ k := by omega
      have ih_res := ih (v + 1) col1 h_le1 h_sz1 h_lt4_1 h_adj_1 h_ok_step
      dsimp at ih_res
      dsimp
      rw [h_res2]
      rcases ih_res with ⟨h_eq_step, h_lt4_final, h_adj_final⟩
      refine ⟨?_, h_lt4_final, h_adj_final⟩
      intro i hi
      have hi_step : i < v + 1 := by omega
      rw [h_eq_step i hi_step]
      have h_i_ne : i ≠ v := by omega
      exact getCol_set_ne col v c i hv_sz h_i_ne
    · have he : extend earlier n v col = (true, col) := by
        rw [extend]
        rw [dif_neg (by omega)]
      have h_col' : (extend earlier n v col).2 = col := by rw [he]
      refine ⟨fun _ _ => by rw [h_col'], ?_, ?_⟩
      · intro i hi
        rw [h_col']
        exact h_lt4 i (by omega)
      · intro i hi u hu h_u_lt
        rw [h_col']
        exact h_adj i (by omega) u hu h_u_lt

/-- Sound earlier-adjacency condition: `earlier` contains all earlier neighbors for each vertex. -/
def IsSoundEarlier (c : Configuration) (earlier : Array (Array Nat)) : Prop :=
  (∀ v < c.totalNodes, ∀ u < v, (c.adj v u = true ∨ c.adj u v = true) → u ∈ (earlier.getD v #[]).data) ∧
  (∀ i < c.ringSize, ∀ u ∈ (earlier.getD i #[]).data, u < i → (c.adj i u = true ∨ c.adj u i = true))

/-- Irreflexivity of adjacency: no vertex is adjacent to itself. -/
def IsIrreflexiveAdj (c : Configuration) : Prop :=
  ∀ i < c.totalNodes, c.adj i i = false

/-- Initial array coloring corresponding to boundary coloring `b`. -/
def initCol (c : Configuration) (b : BoundaryColoring c) : Array Nat :=
  Array.ofFn fun (i : Fin c.totalNodes) =>
    if i.val < c.ringSize then (b i.val).toNat else 0

theorem initCol_size (c : Configuration) (b : BoundaryColoring c) :
    (initCol c b).size = c.totalNodes := by
  dsimp [initCol]
  rw [Array.size_ofFn]

theorem getCol_initCol_ring (c : Configuration) (b : BoundaryColoring c) (i : Nat)
    (hi : i < c.ringSize) (h_tot : c.ringSize ≤ c.totalNodes) :
    getCol (initCol c b) i = (b i).toNat := by
  dsimp [getCol, Array.getD, initCol]
  have hi_tot : i < c.totalNodes := by omega
  have h_sz : i < (Array.ofFn fun (j : Fin c.totalNodes) => if j.val < c.ringSize then (b j.val).toNat else 0).size := by
    rw [Array.size_ofFn]; exact hi_tot
  rw [dif_pos h_sz]
  rw [Array.getElem_ofFn]
  rw [if_pos hi]

set_option linter.unusedVariables false

theorem extend_soundness_of_extend (c : Configuration) (earlier : Array (Array Nat))
    (h_earlier : IsSoundEarlier c earlier)
    (h_irrefl : IsIrreflexiveAdj c)
    (b : BoundaryColoring c)
    (hb : IsValidBoundaryColoring c b)
    (h_ok : (extend earlier c.totalNodes c.ringSize (initCol c b)).1 = true) :
    extendsToInterior c b := by
  have h_r_le : c.ringSize ≤ c.totalNodes := by
    dsimp [Configuration.totalNodes]; omega
  have h_sz : (initCol c b).size ≥ c.totalNodes := by
    rw [initCol_size]; omega
  have h_k : c.totalNodes - c.ringSize ≤ c.totalNodes - c.ringSize := by omega
  have h_lt4_init : ∀ i < c.ringSize, getCol (initCol c b) i < 4 := by
    intro i hi
    rw [getCol_initCol_ring c b i hi h_r_le]
    cases (b i) <;> decide
  have h_adj_init : ∀ i < c.ringSize, ∀ u ∈ (earlier.getD i #[]).data, u < i →
      getCol (initCol c b) u ≠ getCol (initCol c b) i := by
    intro i hi u hu h_u_lt
    have hu_ring : u < c.ringSize := by omega
    rw [getCol_initCol_ring c b i hi h_r_le]
    rw [getCol_initCol_ring c b u hu_ring h_r_le]
    have h_adj_edge := h_earlier.2 i hi u hu h_u_lt
    intro h_eq
    have h_col_eq : b u = b i := by
      have : colorOfNat (b u).toNat = colorOfNat (b i).toNat := by rw [h_eq]
      rw [colorOfNat_toNat, colorOfNat_toNat] at this
      exact this
    cases h_adj_edge with
    | inl h1 =>
      have := hb i u hi hu_ring h1
      exact this h_col_eq.symm
    | inr h2 =>
      have := hb u i hu_ring hi h2
      exact this h_col_eq
  have h_ind := extend_sound_ind earlier c.totalNodes (c.totalNodes - c.ringSize)
    c.ringSize (initCol c b) h_k h_sz h_lt4_init h_adj_init h_ok
  dsimp at h_ind
  rcases h_ind with ⟨h_preserves, h_lt4_all, h_no_conflicts⟩
  let full : Nat → Color := fun i => colorOfNat (getCol (extend earlier c.totalNodes c.ringSize (initCol c b)).2 i)
  refine ⟨full, ?_, ?_⟩
  · intro i hi
    dsimp [full]
    rw [h_preserves i hi]
    rw [getCol_initCol_ring c b i hi h_r_le]
    exact colorOfNat_toNat (b i)
  · intro i j hi hj hadj
    dsimp [full]
    have h_ne : i ≠ j := by
      intro heq
      subst heq
      have := h_irrefl i hi
      rw [this] at hadj
      contradiction
    intro h_eq
    have h_col_eq : getCol (extend earlier c.totalNodes c.ringSize (initCol c b)).2 i =
                    getCol (extend earlier c.totalNodes c.ringSize (initCol c b)).2 j :=
      colorOfNat_inj (h_lt4_all i hi) (h_lt4_all j hj) h_eq
    by_cases h_lt : i < j
    · have h_in : i ∈ (earlier.getD j #[]).data :=
        h_earlier.1 j hj i h_lt (Or.inr hadj)
      have h_diff := h_no_conflicts j hj i h_in h_lt
      exact h_diff h_col_eq
    · have h_gt : j < i := by omega
      have h_in : j ∈ (earlier.getD i #[]).data :=
        h_earlier.1 i hi j h_gt (Or.inl hadj)
      have h_diff := h_no_conflicts i hi j h_in h_gt
      exact h_diff h_col_eq.symm

end Soundness
end Math

