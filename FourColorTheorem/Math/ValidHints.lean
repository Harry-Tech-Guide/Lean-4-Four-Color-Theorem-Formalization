import FourColorTheorem.Math.DischargingAlgo

namespace Math.Discharging

/-- Decidable check that every hint `p` in a list satisfies `p < 5185536` (`p >>> 13 < 633`). -/
def validHintListRec : List Nat → Bool
  | [] => true
  | p :: ps => if Nat.ble 5185536 p then false else validHintListRec ps

/-- Decidable check that every chunk in a list of hint chunks passes `validHintListRec`. -/
def validHintsBlocksRec : List (List Nat) → Bool
  | [] => true
  | b :: bs => if validHintListRec b then validHintsBlocksRec bs else false

/-- Predicate asserting every pending and queued hint in `hs : HintStream` has `p >>> 13 < 633`. -/
def validHintStream (hs : HintStream) : Bool :=
  if validHintListRec hs.1 then validHintsBlocksRec hs.2 else false

theorem validHintListRec_cons_iff (x : Nat) (xs : List Nat) :
    validHintListRec (x :: xs) = true ↔ Nat.ble 5185536 x = false ∧ validHintListRec xs = true := by
  dsimp [validHintListRec]
  cases h : Nat.ble 5185536 x <;> simp

theorem validHintsBlocksRec_cons_iff (b : List Nat) (bs : List (List Nat)) :
    validHintsBlocksRec (b :: bs) = true ↔ validHintListRec b = true ∧ validHintsBlocksRec bs = true := by
  dsimp [validHintsBlocksRec]
  cases validHintListRec b <;> simp

theorem validHintStream_iff (cur : List Nat) (blocks : List (List Nat)) :
    validHintStream (cur, blocks) = true ↔ validHintListRec cur = true ∧ validHintsBlocksRec blocks = true := by
  dsimp [validHintStream]
  cases validHintListRec cur <;> simp

theorem nat_shiftRight_13_lt_633_of_ble_false (p : Nat)
    (h : Nat.ble 5185536 p = false) : Nat.shiftRight p 13 < 633 := by
  have h_not : ¬ (5185536 ≤ p) := by
    intro hle
    have : Nat.ble 5185536 p = true := Nat.ble_eq_true_of_le hle
    rw [this] at h
    contradiction
  have hp : p < 5185536 := by omega
  change p >>> 13 < 633
  rw [Nat.shiftRight_eq_div_pow]
  omega

set_option maxRecDepth 2000000 in
theorem validHints_7 : validHintsBlocksRec hints_7 = true := by rfl

set_option maxRecDepth 2000000 in
theorem validHints_8 : validHintsBlocksRec hints_8 = true := by rfl

set_option maxRecDepth 2000000 in
theorem validHints_9 : validHintsBlocksRec hints_9 = true := by rfl

set_option maxRecDepth 2000000 in
theorem validHints_10 : validHintsBlocksRec hints_10 = true := by rfl

set_option maxRecDepth 2000000 in
theorem validHints_11 : validHintsBlocksRec hints_11 = true := by rfl

/-- All precomputed discharging hints for hub degrees `7 ≤ deg ≤ 11` satisfy `p >>> 13 < 633`. -/
theorem validHintStream_getHintsForDeg (deg : Nat)
    (h_deg : deg = 7 ∨ deg = 8 ∨ deg = 9 ∨ deg = 10 ∨ deg = 11) :
    validHintStream ([], getHintsForDeg deg) = true := by
  rcases h_deg with rfl | rfl | rfl | rfl | rfl
  · dsimp [validHintStream, validHintListRec, getHintsForDeg]; exact validHints_7
  · dsimp [validHintStream, validHintListRec, getHintsForDeg]; exact validHints_8
  · dsimp [validHintStream, validHintListRec, getHintsForDeg]; exact validHints_9
  · dsimp [validHintStream, validHintListRec, getHintsForDeg]; exact validHints_10
  · dsimp [validHintStream, validHintListRec, getHintsForDeg]; exact validHints_11

end Math.Discharging
