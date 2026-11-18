module

/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
Released under Apache 2.0 license.
-/
public import FourColorTheorem.Math.Unavoidability.FastConfEquivData

@[expose] public section

/-!
# 633-Configuration `FastConf` ↔ `RConf` Certificate Block 9
-/

namespace Math.Unavoidability

open Math Math.Discharging

private theorem row_9_0 : checkListZipPrefix fcRow_9_0 rcRow_9_0 = true := rfl
private theorem row_9_1 : checkListZipPrefix fcRow_9_1 rcRow_9_1 = true := rfl
private theorem row_9_2 : checkListZipPrefix fcRow_9_2 rcRow_9_2 = true := rfl
private theorem row_9_3 : checkListZipPrefix fcRow_9_3 rcRow_9_3 = true := rfl
private theorem row_9_4 : checkListZipPrefix fcRow_9_4 rcRow_9_4 = true := rfl
private theorem row_9_5 : checkListZipPrefix fcRow_9_5 rcRow_9_5 = true := rfl
private theorem row_9_6 : checkListZipPrefix fcRow_9_6 rcRow_9_6 = true := rfl
private theorem row_9_7 : checkListZipPrefix fcRow_9_7 rcRow_9_7 = true := rfl

theorem equiv_blk_9 (r : Nat) (hr : r < 8) :
    checkListZipPrefix
      (fcBlk_9[r]'(by rw [fcBlk_9_len]; exact hr))
      (rcBlk_9[r]'(by rw [rcBlk_9_len]; exact hr)) = true := by
  match r with
  | 0 => exact row_9_0
  | 1 => exact row_9_1
  | 2 => exact row_9_2
  | 3 => exact row_9_3
  | 4 => exact row_9_4
  | 5 => exact row_9_5
  | 6 => exact row_9_6
  | 7 => exact row_9_7
  | _ + 8 => omega

end Math.Unavoidability
