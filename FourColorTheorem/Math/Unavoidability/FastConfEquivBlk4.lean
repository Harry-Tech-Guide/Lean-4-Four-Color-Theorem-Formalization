/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
Released under Apache 2.0 license.
-/
import FourColorTheorem.Math.Unavoidability.FastConfEquivData

/-!
# 633-Configuration `FastConf` ↔ `RConf` Certificate Block 4
-/

namespace Math.Unavoidability

open Math Math.Discharging

private theorem row_4_0 : checkListZipPrefix fcRow_4_0 rcRow_4_0 = true := rfl
private theorem row_4_1 : checkListZipPrefix fcRow_4_1 rcRow_4_1 = true := rfl
private theorem row_4_2 : checkListZipPrefix fcRow_4_2 rcRow_4_2 = true := rfl
private theorem row_4_3 : checkListZipPrefix fcRow_4_3 rcRow_4_3 = true := rfl
private theorem row_4_4 : checkListZipPrefix fcRow_4_4 rcRow_4_4 = true := rfl
private theorem row_4_5 : checkListZipPrefix fcRow_4_5 rcRow_4_5 = true := rfl
private theorem row_4_6 : checkListZipPrefix fcRow_4_6 rcRow_4_6 = true := rfl
private theorem row_4_7 : checkListZipPrefix fcRow_4_7 rcRow_4_7 = true := rfl

theorem equiv_blk_4 (r : Nat) (hr : r < 8) :
    checkListZipPrefix
      (fcBlk_4[r]'(by rw [fcBlk_4_len]; exact hr))
      (rcBlk_4[r]'(by rw [rcBlk_4_len]; exact hr)) = true := by
  match r with
  | 0 => exact row_4_0
  | 1 => exact row_4_1
  | 2 => exact row_4_2
  | 3 => exact row_4_3
  | 4 => exact row_4_4
  | 5 => exact row_4_5
  | 6 => exact row_4_6
  | 7 => exact row_4_7
  | _ + 8 => omega

end Math.Unavoidability
