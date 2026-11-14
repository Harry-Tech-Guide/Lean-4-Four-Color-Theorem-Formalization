/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
Released under Apache 2.0 license.
-/
import FourColorTheorem.Math.Unavoidability.FastConfEquivData

/-!
# 633-Configuration `FastConf` ↔ `RConf` Certificate Block 7
-/

namespace Math.Unavoidability

open Math Math.Discharging

private theorem row_7_0 : checkListZipPrefix fcRow_7_0 rcRow_7_0 = true := rfl
private theorem row_7_1 : checkListZipPrefix fcRow_7_1 rcRow_7_1 = true := rfl
private theorem row_7_2 : checkListZipPrefix fcRow_7_2 rcRow_7_2 = true := rfl
private theorem row_7_3 : checkListZipPrefix fcRow_7_3 rcRow_7_3 = true := rfl
private theorem row_7_4 : checkListZipPrefix fcRow_7_4 rcRow_7_4 = true := rfl
private theorem row_7_5 : checkListZipPrefix fcRow_7_5 rcRow_7_5 = true := rfl
private theorem row_7_6 : checkListZipPrefix fcRow_7_6 rcRow_7_6 = true := rfl
private theorem row_7_7 : checkListZipPrefix fcRow_7_7 rcRow_7_7 = true := rfl

theorem equiv_blk_7 (r : Nat) (hr : r < 8) :
    checkListZipPrefix
      (fcBlk_7[r]'(by rw [fcBlk_7_len]; exact hr))
      (rcBlk_7[r]'(by rw [rcBlk_7_len]; exact hr)) = true := by
  match r with
  | 0 => exact row_7_0
  | 1 => exact row_7_1
  | 2 => exact row_7_2
  | 3 => exact row_7_3
  | 4 => exact row_7_4
  | 5 => exact row_7_5
  | 6 => exact row_7_6
  | 7 => exact row_7_7
  | _ + 8 => omega

end Math.Unavoidability
