/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
Released under Apache 2.0 license.
-/
import FourColorTheorem.Math.Unavoidability.FastConfEquivData

/-!
# 633-Configuration `FastConf` ↔ `RConf` Certificate Block 8
-/

namespace Math.Unavoidability

open Math Math.Discharging

private theorem row_8_0 : checkListZipPrefix fcRow_8_0 rcRow_8_0 = true := rfl
private theorem row_8_1 : checkListZipPrefix fcRow_8_1 rcRow_8_1 = true := rfl
private theorem row_8_2 : checkListZipPrefix fcRow_8_2 rcRow_8_2 = true := rfl
private theorem row_8_3 : checkListZipPrefix fcRow_8_3 rcRow_8_3 = true := rfl
private theorem row_8_4 : checkListZipPrefix fcRow_8_4 rcRow_8_4 = true := rfl
private theorem row_8_5 : checkListZipPrefix fcRow_8_5 rcRow_8_5 = true := rfl
private theorem row_8_6 : checkListZipPrefix fcRow_8_6 rcRow_8_6 = true := rfl
private theorem row_8_7 : checkListZipPrefix fcRow_8_7 rcRow_8_7 = true := rfl

theorem equiv_blk_8 (r : Nat) (hr : r < 8) :
    checkListZipPrefix
      (fcBlk_8[r]'(by rw [fcBlk_8_len]; exact hr))
      (rcBlk_8[r]'(by rw [rcBlk_8_len]; exact hr)) = true := by
  match r with
  | 0 => exact row_8_0
  | 1 => exact row_8_1
  | 2 => exact row_8_2
  | 3 => exact row_8_3
  | 4 => exact row_8_4
  | 5 => exact row_8_5
  | 6 => exact row_8_6
  | 7 => exact row_8_7
  | _ + 8 => omega

end Math.Unavoidability
