/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
Released under Apache 2.0 license.
-/
import FourColorTheorem.Math.Unavoidability.FastConfEquivData

/-!
# 633-Configuration `FastConf` ↔ `RConf` Certificate Block 2
-/

namespace Math.Unavoidability

open Math Math.Discharging

private theorem row_2_0 : checkListZipPrefix fcRow_2_0 rcRow_2_0 = true := rfl
private theorem row_2_1 : checkListZipPrefix fcRow_2_1 rcRow_2_1 = true := rfl
private theorem row_2_2 : checkListZipPrefix fcRow_2_2 rcRow_2_2 = true := rfl
private theorem row_2_3 : checkListZipPrefix fcRow_2_3 rcRow_2_3 = true := rfl
private theorem row_2_4 : checkListZipPrefix fcRow_2_4 rcRow_2_4 = true := rfl
private theorem row_2_5 : checkListZipPrefix fcRow_2_5 rcRow_2_5 = true := rfl
private theorem row_2_6 : checkListZipPrefix fcRow_2_6 rcRow_2_6 = true := rfl
private theorem row_2_7 : checkListZipPrefix fcRow_2_7 rcRow_2_7 = true := rfl

theorem equiv_blk_2 (r : Nat) (hr : r < 8) :
    checkListZipPrefix
      (fcBlk_2[r]'(by rw [fcBlk_2_len]; exact hr))
      (rcBlk_2[r]'(by rw [rcBlk_2_len]; exact hr)) = true := by
  match r with
  | 0 => exact row_2_0
  | 1 => exact row_2_1
  | 2 => exact row_2_2
  | 3 => exact row_2_3
  | 4 => exact row_2_4
  | 5 => exact row_2_5
  | 6 => exact row_2_6
  | 7 => exact row_2_7
  | _ + 8 => omega

end Math.Unavoidability
