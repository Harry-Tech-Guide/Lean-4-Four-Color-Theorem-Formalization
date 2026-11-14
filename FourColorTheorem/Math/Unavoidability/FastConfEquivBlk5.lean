/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
Released under Apache 2.0 license.
-/
import FourColorTheorem.Math.Unavoidability.FastConfEquivData

/-!
# 633-Configuration `FastConf` ↔ `RConf` Certificate Block 5
-/

namespace Math.Unavoidability

open Math Math.Discharging

private theorem row_5_0 : checkListZipPrefix fcRow_5_0 rcRow_5_0 = true := rfl
private theorem row_5_1 : checkListZipPrefix fcRow_5_1 rcRow_5_1 = true := rfl
private theorem row_5_2 : checkListZipPrefix fcRow_5_2 rcRow_5_2 = true := rfl
private theorem row_5_3 : checkListZipPrefix fcRow_5_3 rcRow_5_3 = true := rfl
private theorem row_5_4 : checkListZipPrefix fcRow_5_4 rcRow_5_4 = true := rfl
private theorem row_5_5 : checkListZipPrefix fcRow_5_5 rcRow_5_5 = true := rfl
private theorem row_5_6 : checkListZipPrefix fcRow_5_6 rcRow_5_6 = true := rfl
private theorem row_5_7 : checkListZipPrefix fcRow_5_7 rcRow_5_7 = true := rfl

theorem equiv_blk_5 (r : Nat) (hr : r < 8) :
    checkListZipPrefix
      (fcBlk_5[r]'(by rw [fcBlk_5_len]; exact hr))
      (rcBlk_5[r]'(by rw [rcBlk_5_len]; exact hr)) = true := by
  match r with
  | 0 => exact row_5_0
  | 1 => exact row_5_1
  | 2 => exact row_5_2
  | 3 => exact row_5_3
  | 4 => exact row_5_4
  | 5 => exact row_5_5
  | 6 => exact row_5_6
  | 7 => exact row_5_7
  | _ + 8 => omega

end Math.Unavoidability
