/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
Released under Apache 2.0 license.
-/
import FourColorTheorem.Math.Unavoidability.FastConfEquivData

/-!
# 633-Configuration `FastConf` ↔ `RConf` Certificate Block 3
-/

namespace Math.Unavoidability

open Math Math.Discharging

private theorem row_3_0 : checkListZipPrefix fcRow_3_0 rcRow_3_0 = true := rfl
private theorem row_3_1 : checkListZipPrefix fcRow_3_1 rcRow_3_1 = true := rfl
private theorem row_3_2 : checkListZipPrefix fcRow_3_2 rcRow_3_2 = true := rfl
private theorem row_3_3 : checkListZipPrefix fcRow_3_3 rcRow_3_3 = true := rfl
private theorem row_3_4 : checkListZipPrefix fcRow_3_4 rcRow_3_4 = true := rfl
private theorem row_3_5 : checkListZipPrefix fcRow_3_5 rcRow_3_5 = true := rfl
private theorem row_3_6 : checkListZipPrefix fcRow_3_6 rcRow_3_6 = true := rfl
private theorem row_3_7 : checkListZipPrefix fcRow_3_7 rcRow_3_7 = true := rfl

theorem equiv_blk_3 (r : Nat) (hr : r < 8) :
    checkListZipPrefix
      (fcBlk_3[r]'(by rw [fcBlk_3_len]; exact hr))
      (rcBlk_3[r]'(by rw [rcBlk_3_len]; exact hr)) = true := by
  match r with
  | 0 => exact row_3_0
  | 1 => exact row_3_1
  | 2 => exact row_3_2
  | 3 => exact row_3_3
  | 4 => exact row_3_4
  | 5 => exact row_3_5
  | 6 => exact row_3_6
  | 7 => exact row_3_7
  | _ + 8 => omega

end Math.Unavoidability
