module

public import FourColorTheorem.Math.Soundness.CReduce

@[expose] public section

set_option linter.unusedVariables false
set_option linter.constructorNameAsVariable false

namespace Math
namespace Soundness

open FastReducer
open Batch

/-!
# Soundness of `runContractCheckTotal` (`ContractCheckSoundnessHypothesis`)

This module proves `ContractCheckSoundnessHypothesis` (`contractCheckSoundness_of_wellFormed`):
when `runContractCheckTotal (rconfOfConfig c earlier) pow3 live = true`, for any configuration `c`
with a valid ring cycle (`IsRingCycle`), well-formed earlier table (`IsWellFormedEarlier c earlier`),
and binary live array (`∀ j, live.get! j = 0 ∨ live.get! j = 1`), every valid boundary coloring
`b` that extends to the contracted configuration (`extendsToContracted c b`) has
`live.get! (boundaryTrace c b pow3) = 0`.
-/

/-!
### 1. Klein Four-Group (`V₄`) XOR Shift Normalization
-/

/-- Shift a color `col : Color` by XOR with `dCol : Color` in `V₄`. -/
def xorColor (col dCol : Color) : Color :=
  colorOfNat (col.toNat ^^^ dCol.toNat)

theorem toNat_lt_four (col : Color) : col.toNat < 4 := by
  cases col <;> decide

theorem toNat_xorColor (col dCol : Color) :
    (xorColor col dCol).toNat = col.toNat ^^^ dCol.toNat := by
  cases col <;> cases dCol <;> rfl

theorem xorColor_self (col : Color) : (xorColor col col).toNat = 0 := by
  cases col <;> rfl

theorem xorColor_inj {c1 c2 dCol : Color}
    (h : xorColor c1 dCol = xorColor c2 dCol) : c1 = c2 := by
  revert h
  cases c1 <;> cases c2 <;> cases dCol <;> decide

theorem xorColor_diff (c1 c2 dCol : Color) :
    (xorColor c1 dCol).toNat ^^^ (xorColor c2 dCol).toNat = c1.toNat ^^^ c2.toNat := by
  cases c1 <;> cases c2 <;> cases dCol <;> rfl

/-- Shift an entire vertex coloring `f : Nat → Color` by XOR with `dCol : Color`. -/
def xorShiftColoring (f : Nat → Color) (dCol : Color) : Nat → Color :=
  fun u => xorColor (f u) dCol

theorem boundaryTraceAux_xorShift (r : Nat) (b : Nat → Color) (pow3 : Array Nat)
    (dCol : Color) (rem i acc : Nat) :
    boundaryTraceAux r (xorShiftColoring b dCol) pow3 rem i acc =
      boundaryTraceAux r b pow3 rem i acc := by
  induction rem generalizing i acc with
  | zero => rfl
  | succ rem ih =>
    simp only [boundaryTraceAux, xorShiftColoring, xorColor_diff]
    exact ih (i + 1) _

theorem boundaryTrace_xorShift (c : Configuration) (b : BoundaryColoring c)
    (pow3 : Array Nat) (dCol : Color) :
    boundaryTrace c (xorShiftColoring b dCol) pow3 = boundaryTrace c b pow3 :=
  boundaryTraceAux_xorShift c.ringSize b pow3 dCol c.ringSize 0 0

theorem validBoundary_xorShift (c : Configuration) (b : BoundaryColoring c)
    (hb : IsValidBoundaryColoring c b) (dCol : Color) :
    IsValidBoundaryColoring c (xorShiftColoring b dCol) := by
  intro i j hi hj hadj h_eq
  exact hb i j hi hj hadj (xorColor_inj h_eq)

theorem validContract_xorShift (c : Configuration) (full : Nat → Color)
    (hf : IsValidContractColoring c full) (dCol : Color) :
    IsValidContractColoring c (xorShiftColoring full dCol) := by
  constructor
  · intro uv huv
    rcases hf.1 uv huv with ⟨h1, h2, h_eq⟩
    refine ⟨h1, h2, ?_⟩
    dsimp [xorShiftColoring]
    rw [h_eq]
  · intro i j hi hj hadj hnot_contr h_eq
    exact hf.2 i j hi hj hadj hnot_contr (xorColor_inj h_eq)

/-!
### 2. Leaf Trace Equivalence (`contractLeafAux`)
-/

theorem xor_pos_of_ne (c1 c2 : Color) (h_ne : c1 ≠ c2) :
    (c1.toNat ^^^ c2.toNat == 0) = false ∧ c1.toNat ^^^ c2.toNat > 0 := by
  revert h_ne
  cases c1 <;> cases c2 <;> decide

theorem contractLeafAux_eq_boundaryTraceAux (c : Configuration)
    (h_ring : c.ringSize ≥ 2 ∧ ∀ i < c.ringSize, c.adj i ((i + 1) % c.ringSize) = true)
    (b : BoundaryColoring c) (hb : IsValidBoundaryColoring c b)
    (col : Array Nat) (pow3 : Array Nat) (live : ByteArray)
    (h_agree : ∀ i < c.ringSize, getCol col i = (b i).toNat)
    (rem i acc : Nat) (h_le : i + rem ≤ c.ringSize) :
    contractLeafAux c.ringSize col pow3 live rem i acc =
      !(live.get! (boundaryTraceAux c.ringSize b pow3 rem i acc) == 1) := by
  induction rem generalizing i acc with
  | zero => rfl
  | succ rem ih =>
    have hi : i < c.ringSize := by omega
    have h_nxt : (i + 1) % c.ringSize < c.ringSize :=
      Nat.mod_lt (i + 1) (by omega)
    have hadj : c.adj i ((i + 1) % c.ringSize) = true := h_ring.2 i hi
    have h_ne : b i ≠ b ((i + 1) % c.ringSize) := hb i ((i + 1) % c.ringSize) hi h_nxt hadj
    rcases xor_pos_of_ne (b i) (b ((i + 1) % c.ringSize)) h_ne with ⟨h_not_zero, h_pos⟩
    dsimp [contractLeafAux, boundaryTraceAux]
    rw [h_agree i hi, h_agree ((i + 1) % c.ringSize) h_nxt]
    rw [if_neg (by rw [h_not_zero]; decide), if_pos h_pos]
    exact ih (i + 1) _ (by omega)

theorem live_zero_of_contractLeafAux (c : Configuration)
    (h_ring : c.ringSize ≥ 2 ∧ ∀ i < c.ringSize, c.adj i ((i + 1) % c.ringSize) = true)
    (b : BoundaryColoring c) (hb : IsValidBoundaryColoring c b)
    (col : Array Nat) (pow3 : Array Nat) (live : ByteArray)
    (h_agree : ∀ i < c.ringSize, getCol col i = (b i).toNat)
    (h_bin : ∀ j, live.get! j = 0 ∨ live.get! j = 1)
    (h_leaf : contractLeafAux c.ringSize col pow3 live c.ringSize 0 0 = true) :
    live.get! (boundaryTrace c b pow3) = 0 := by
  rw [contractLeafAux_eq_boundaryTraceAux c h_ring b hb col pow3 live h_agree c.ringSize 0 0 (by omega)] at h_leaf
  unfold boundaryTrace
  rcases h_bin (boundaryTraceAux c.ringSize b pow3 c.ringSize 0 0) with h0 | h1
  · exact h0
  · rw [h1] at h_leaf
    contradiction

/-!
### 3. Contract Alias Invariant (`computeContractAlias`)
-/

/-- Invariant: every vertex `w < c.totalNodes` maps to `getCol al w < c.totalNodes`
    sharing the same color under `full`. -/
def AliasColorSound (c : Configuration) (full : Nat → Color) (al : Array Nat) : Prop :=
  ∀ w < c.totalNodes, getCol al w < c.totalNodes ∧ full (getCol al w) = full w

theorem getCol_set!_cases (al : Array Nat) (idx val w : Nat) :
    (w = idx ∧ getCol (al.set! idx val) w = val) ∨ getCol (al.set! idx val) w = getCol al w := by
  by_cases h_in : idx < al.size
  · by_cases hw : w = idx
    · subst hw
      exact Or.inl ⟨rfl, getCol_set_eq al w val h_in⟩
    · exact Or.inr (getCol_set_ne al idx val w h_in hw)
  · right
    dsimp [Array.set!, Array.setIfInBounds]
    rw [dif_neg h_in]

theorem aliasColorSound_set! (c : Configuration) (full : Nat → Color) (al : Array Nat)
    (idx mn : Nat) (h_al : AliasColorSound c full al)
    (h_mn_lt : mn < c.totalNodes)
    (h_mn_col : idx < c.totalNodes → full mn = full idx) :
    AliasColorSound c full (al.set! idx mn) := by
  intro w hw
  rcases getCol_set!_cases al idx mn w with ⟨rfl, h_eq⟩ | h_eq
  · rw [h_eq]
    exact ⟨h_mn_lt, h_mn_col hw⟩
  · rw [h_eq]
    exact h_al w hw

theorem aliasColorSound_relaxContractEdge (c : Configuration) (full : Nat → Color)
    (hf : IsValidContractColoring c full) (al : Array Nat)
    (uv : Nat × Nat) (huv : uv ∈ c.contractEdges)
    (h_al : AliasColorSound c full al) :
    AliasColorSound c full (relaxContractEdge al uv) := by
  rcases hf.1 uv huv with ⟨hu_lt, hv_lt, huv_col⟩
  rcases h_al uv.1 hu_lt with ⟨hru_lt, hru_col⟩
  rcases h_al uv.2 hv_lt with ⟨hrv_lt, hrv_col⟩
  let ru := getCol al uv.1
  let rv := getCol al uv.2
  let mn := min ru rv
  have h_mn_cases : mn = ru ∨ mn = rv := by
    dsimp [mn]
    by_cases h : ru ≤ rv
    · exact Or.inl (Nat.min_eq_left h)
    · exact Or.inr (Nat.min_eq_right (by omega))
  have h_mn_lt : mn < c.totalNodes := by
    rcases h_mn_cases with h | h <;> omega
  have h_mn_col_u : full mn = full uv.1 := by
    rcases h_mn_cases with h | h
    · rw [h]; exact hru_col
    · rw [h, hrv_col, ← huv_col]
  have h_mn_col_v : full mn = full uv.2 := by
    rw [← huv_col]; exact h_mn_col_u
  have h_mn_col_ru : full mn = full ru := by
    rw [hru_col]; exact h_mn_col_u
  have h_mn_col_rv : full mn = full rv := by
    rw [hrv_col]; exact h_mn_col_v
  dsimp [relaxContractEdge]
  apply aliasColorSound_set! c full _ rv mn
  · apply aliasColorSound_set! c full _ ru mn
    · apply aliasColorSound_set! c full _ uv.2 mn
      · exact aliasColorSound_set! c full al uv.1 mn h_al h_mn_lt (fun _ => h_mn_col_u)
      · exact h_mn_lt
      · exact fun _ => h_mn_col_v
    · exact h_mn_lt
    · exact fun _ => h_mn_col_ru
  · exact h_mn_lt
  · exact fun _ => h_mn_col_rv

theorem aliasColorSound_relaxContractEdgesList (c : Configuration) (full : Nat → Color)
    (hf : IsValidContractColoring c full) (edges : List (Nat × Nat))
    (h_sub : ∀ uv ∈ edges, uv ∈ c.contractEdges)
    (al : Array Nat) (h_al : AliasColorSound c full al) :
    AliasColorSound c full (relaxContractEdgesList edges al) := by
  induction edges generalizing al with
  | nil => exact h_al
  | cons uv rest ih =>
    dsimp [relaxContractEdgesList]
    exact ih (fun x hx => h_sub x (List.mem_cons_of_mem uv hx))
      (relaxContractEdge al uv)
      (aliasColorSound_relaxContractEdge c full hf al uv (h_sub uv (List.mem_cons_self ..)) h_al)

theorem aliasColorSound_computeContractAliasLoop (c : Configuration) (full : Nat → Color)
    (hf : IsValidContractColoring c full) (k : Nat) (edges : List (Nat × Nat))
    (h_sub : ∀ uv ∈ edges, uv ∈ c.contractEdges)
    (al : Array Nat) (h_al : AliasColorSound c full al) :
    AliasColorSound c full (computeContractAliasLoop k edges al) := by
  induction k generalizing al with
  | zero => exact h_al
  | succ k ih =>
    dsimp [computeContractAliasLoop]
    exact ih (relaxContractEdgesList edges al)
      (aliasColorSound_relaxContractEdgesList c full hf edges h_sub al h_al)

theorem getCol_range (n w : Nat) (hw : w < n) :
    getCol (Array.range n) w = w := by
  simp [getCol, Array.getD, hw]

theorem aliasColorSound_init (c : Configuration) (full : Nat → Color) :
    AliasColorSound c full (Array.range c.totalNodes) := by
  intro w hw
  rw [getCol_range c.totalNodes w hw]
  exact ⟨hw, rfl⟩

theorem aliasColorSound_computeContractAlias (c : Configuration) (earlier : Array (Array Nat))
    (full : Nat → Color) (hf : IsValidContractColoring c full) :
    AliasColorSound c full (computeContractAlias (rconfOfConfig c earlier)) := by
  dsimp [computeContractAlias, rconfOfConfig]
  exact aliasColorSound_computeContractAliasLoop c full hf c.totalNodes c.contractEdges
    (fun uv huv => huv) (Array.range c.totalNodes) (aliasColorSound_init c full)

theorem checkAliasClosed_sound (edges : List (Nat × Nat)) (alias : Array Nat)
    (h : checkAliasClosed edges alias = true) :
    ∀ uv ∈ edges, getCol alias uv.1 = getCol alias uv.2 := by
  intro uv huv
  dsimp [checkAliasClosed] at h
  exact beq_iff_eq.mp (List.all_eq_true.mp h uv huv)

theorem not_contractEdge_of_alias_ne (edges : List (Nat × Nat)) (alias : Array Nat)
    (h_closed : ∀ uv ∈ edges, getCol alias uv.1 = getCol alias uv.2)
    (v u : Nat) (h_ne : getCol alias u ≠ getCol alias v) :
    isContractEdge edges v u = false := by
  dsimp [isContractEdge]
  rw [Bool.or_eq_false_iff]
  constructor
  · cases h1 : edges.contains (v, u) with
    | false => rfl
    | true =>
      have h_mem : (v, u) ∈ edges := List.contains_iff_mem.mp h1
      have h_eq := h_closed (v, u) h_mem
      exact False.elim (h_ne h_eq.symm)
  · cases h2 : edges.contains (u, v) with
    | false => rfl
    | true =>
      have h_mem : (u, v) ∈ edges := List.contains_iff_mem.mp h2
      have h_eq := h_closed (u, v) h_mem
      exact False.elim (h_ne h_eq)

/-!
### 4. Backtracking Completeness of `checkContractExactTotal`
-/

theorem contractColorFree_of_validContract (c : Configuration) (earlier : Array (Array Nat))
    (h_wf : IsWellFormedEarlier c earlier)
    (full : Nat → Color) (hf : IsValidContractColoring c full)
    (alias col : Array Nat)
    (h_closed : ∀ uv ∈ c.contractEdges, getCol alias uv.1 = getCol alias uv.2)
    (v : Nat) (hv : v < c.totalNodes)
    (h_agree : ∀ u < v, getCol col u = (full u).toNat) :
    contractColorFree (earlier.getD v #[]) alias col (getCol alias v) (full v).toNat = true := by
  dsimp [contractColorFree]
  apply List.all_eq_true.mpr
  intro u hu
  rcases h_wf v hv u hu with ⟨hu_lt, hadj⟩
  by_cases h_al : getCol alias u = getCol alias v
  · rw [Bool.or_eq_true]
    exact Or.inl (beq_iff_eq.mpr h_al)
  · rw [Bool.or_eq_true]
    right
    rw [h_agree u hu_lt]
    apply bne_iff_ne.mpr
    intro h_nat_eq
    have h_col_eq : full u = full v := by
      have : colorOfNat (full u).toNat = colorOfNat (full v).toNat := by rw [h_nat_eq]
      rwa [colorOfNat_toNat, colorOfNat_toNat] at this
    have h_not_ce := not_contractEdge_of_alias_ne c.contractEdges alias h_closed v u h_al
    have hu_tot : u < c.totalNodes := by omega
    exact hf.2 v u hv hu_tot hadj h_not_ce h_col_eq.symm

theorem checkContractExactTotal_sound_ind (c : Configuration) (earlier : Array (Array Nat))
    (h_wf : IsWellFormedEarlier c earlier)
    (full : Nat → Color) (hf : IsValidContractColoring c full)
    (alias pow3 : Array Nat) (live : ByteArray)
    (h_al_col : AliasColorSound c full alias)
    (h_closed : ∀ uv ∈ c.contractEdges, getCol alias uv.1 = getCol alias uv.2)
    (fuel v : Nat) (col : Array Nat)
    (h_fuel : c.totalNodes - v ≤ fuel)
    (h_sz : col.size ≥ c.totalNodes)
    (h_agree : ∀ u < v, getCol col u = (full u).toNat)
    (h_chk : checkContractExactTotal fuel earlier alias c.totalNodes c.ringSize v col pow3 live = true) :
    ∃ col_final : Array Nat,
      (∀ i < c.ringSize, getCol col_final i = (full i).toNat) ∧
      contractLeafAux c.ringSize col_final pow3 live c.ringSize 0 0 = true := by
  induction fuel generalizing v col with
  | zero =>
    have hv_ge : v ≥ c.totalNodes := by omega
    have h_r_le : c.ringSize ≤ v := by
      have : c.totalNodes = c.ringSize + c.interiorSize := rfl
      omega
    dsimp [checkContractExactTotal] at h_chk
    exact ⟨col, fun i hi => h_agree i (by omega), h_chk⟩
  | succ fuel ih =>
    dsimp [checkContractExactTotal] at h_chk
    by_cases hv_ge : v ≥ c.totalNodes
    · rw [if_pos hv_ge] at h_chk
      have h_r_le : c.ringSize ≤ v := by
        have : c.totalNodes = c.ringSize + c.interiorSize := rfl
        omega
      exact ⟨col, fun i hi => h_agree i (by omega), h_chk⟩
    · rw [if_neg hv_ge] at h_chk
      have hv_lt : v < c.totalNodes := by omega
      have h_cf := contractColorFree_of_validContract c earlier h_wf full hf alias col h_closed v hv_lt h_agree
      let cv := (full v).toNat
      let col1 := col.set! v cv
      have h_sz1 : col1.size ≥ c.totalNodes := by
        rw [size_set!]; exact h_sz
      have hv_sz : v < col.size := by omega
      have h_agree1 : ∀ u < v + 1, getCol col1 u = (full u).toNat := by
        intro u hu
        by_cases huv : u = v
        · subst huv
          exact getCol_set_eq col u cv hv_sz
        ·exact (getCol_set_ne col v cv u hv_sz huv).trans (h_agree u (by omega))
      have h_fuel1 : c.totalNodes - (v + 1) ≤ fuel := by omega
      by_cases h_root : getCol alias v < v
      · rw [if_pos h_root] at h_chk
        have h_root_col : getCol col (getCol alias v) = cv := by
          rw [h_agree (getCol alias v) h_root]
          rcases h_al_col v hv_lt with ⟨_, h_eq_col⟩
          rw [h_eq_col]
        rw [h_root_col, if_pos h_cf] at h_chk
        exact ih (v + 1) col1 h_fuel1 h_sz1 h_agree1 h_chk
      · rw [if_neg h_root] at h_chk
        rcases Bool.and_eq_true_iff.mp h_chk with ⟨h012, h3⟩
        rcases Bool.and_eq_true_iff.mp h012 with ⟨h01, h2⟩
        rcases Bool.and_eq_true_iff.mp h01 with ⟨h0, h1⟩
        have hcv_lt : cv < 4 := toNat_lt_four (full v)
        have hcv_cases : cv = 0 ∨ cv = 1 ∨ cv = 2 ∨ cv = 3 := by omega
        change contractColorFree (earlier.getD v #[]) alias col (getCol alias v) cv = true at h_cf
        have h_step : checkContractExactTotal fuel earlier alias c.totalNodes c.ringSize (v + 1) col1 pow3 live = true := by
          rcases hcv_cases with h_c | h_c | h_c | h_c
          · dsimp [col1]; rw [h_c] at h_cf ⊢; rw [if_pos h_cf] at h0; exact h0
          · dsimp [col1]; rw [h_c] at h_cf ⊢; rw [if_pos h_cf] at h1; exact h1
          · dsimp [col1]; rw [h_c] at h_cf ⊢; rw [if_pos h_cf] at h2; exact h2
          · dsimp [col1]; rw [h_c] at h_cf ⊢; rw [if_pos h_cf] at h3; exact h3
        exact ih (v + 1) col1 h_fuel1 h_sz1 h_agree1 h_step

theorem getCol_replicate_zero (n u : Nat) :
    getCol (Array.replicate n 0) u = 0 := by
  dsimp [getCol, Array.getD]
  split
  · simp
  · rfl

/-- **Main Theorem C2 (`contractCheckSoundness_of_wellFormed`):**
    For any configuration `c` with a valid ring cycle (`c.ringSize ≥ 2` and consecutive ring adjacency),
    well-formed earlier table (`IsWellFormedEarlier c earlier`), and binary live array,
    `ContractCheckSoundnessHypothesis c earlier pow3 live` holds unconditionally. -/
theorem contractCheckSoundness_of_wellFormed (c : Configuration) (earlier : Array (Array Nat))
    (pow3 : Array Nat) (live : ByteArray)
    (h_ring : c.ringSize ≥ 2 ∧ ∀ i < c.ringSize, c.adj i ((i + 1) % c.ringSize) = true)
    (h_wf : IsWellFormedEarlier c earlier)
    (h_bin : ∀ j, live.get! j = 0 ∨ live.get! j = 1) :
    ContractCheckSoundnessHypothesis c earlier pow3 live := by
  intro h_run b hb ⟨full0, h_ring_eq0, hf0⟩
  dsimp [runContractCheckTotal] at h_run
  rcases Bool.and_eq_true_iff.mp h_run with ⟨h_closed_bool, h_chk⟩
  let dCol := full0 0
  let full := xorShiftColoring full0 dCol
  let b' := xorShiftColoring b dCol
  have hf : IsValidContractColoring c full := validContract_xorShift c full0 hf0 dCol
  have hb' : IsValidBoundaryColoring c b' := validBoundary_xorShift c b hb dCol
  have h_full0_zero : (full 0).toNat = 0 := xorColor_self (full0 0)
  let rc := rconfOfConfig c earlier
  let alias := computeContractAlias rc
  have h_al_col : AliasColorSound c full alias :=
    aliasColorSound_computeContractAlias c earlier full hf
  have h_closed : ∀ uv ∈ c.contractEdges, getCol alias uv.1 = getCol alias uv.2 := by
    have h_cl := checkAliasClosed_sound rc.contractEdges.toList alias h_closed_bool
    simpa [rc, rconfOfConfig] using h_cl
  have h_agree0 : ∀ u < 1, getCol (Array.replicate c.totalNodes 0) u = (full u).toNat := by
    intro u hu
    have hu0 : u = 0 := by omega
    subst hu0
    rw [getCol_replicate_zero, h_full0_zero]
  have h_sz0 : (Array.replicate c.totalNodes 0).size ≥ c.totalNodes := by
    rw [Array.size_replicate]; exact Nat.le_refl _
  rcases checkContractExactTotal_sound_ind c earlier h_wf full hf alias pow3 live
      h_al_col h_closed c.totalNodes 1 (Array.replicate c.totalNodes 0)
      (by omega) h_sz0 h_agree0 h_chk with ⟨col_final, h_final_agree, h_leaf⟩
  have h_final_b' : ∀ i < c.ringSize, getCol col_final i = (b' i).toNat := by
    intro i hi
    rw [h_final_agree i hi]
    dsimp [full, b', xorShiftColoring]
    rw [h_ring_eq0 i hi]
  have h_lz' := live_zero_of_contractLeafAux c h_ring b' hb' col_final pow3 live h_final_b' h_bin h_leaf
  rwa [boundaryTrace_xorShift c b pow3 dCol] at h_lz'

end Soundness
end Math
