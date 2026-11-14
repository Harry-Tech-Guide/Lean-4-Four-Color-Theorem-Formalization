/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
Released under Apache 2.0 license.
-/
import FourColorTheorem.Math.Unavoidability.FastConfEquivData

/-!
# 633-Configuration `FastConf` ↔ `RConf` Certificate Block 0
-/

namespace Math.Unavoidability

open Math Math.Discharging

private theorem row_0_0 : checkListZipPrefix fcRow_0_0 rcRow_0_0 = true := rfl
private theorem row_0_1 : checkListZipPrefix fcRow_0_1 rcRow_0_1 = true := rfl
private theorem row_0_2 : checkListZipPrefix fcRow_0_2 rcRow_0_2 = true := rfl
private theorem row_0_3 : checkListZipPrefix fcRow_0_3 rcRow_0_3 = true := rfl
private theorem row_0_4 : checkListZipPrefix fcRow_0_4 rcRow_0_4 = true := rfl
private theorem row_0_5 : checkListZipPrefix fcRow_0_5 rcRow_0_5 = true := rfl
private theorem row_0_6 : checkListZipPrefix fcRow_0_6 rcRow_0_6 = true := rfl
private theorem row_0_7 : checkListZipPrefix fcRow_0_7 rcRow_0_7 = true := rfl

theorem equiv_blk_0 (r : Nat) (hr : r < 8) :
    checkListZipPrefix
      (fcBlk_0[r]'(by rw [fcBlk_0_len]; exact hr))
      (rcBlk_0[r]'(by rw [rcBlk_0_len]; exact hr)) = true := by
  match r with
  | 0 => exact row_0_0
  | 1 => exact row_0_1
  | 2 => exact row_0_2
  | 3 => exact row_0_3
  | 4 => exact row_0_4
  | 5 => exact row_0_5
  | 6 => exact row_0_6
  | 7 => exact row_0_7
  | _ + 8 => omega

end Math.Unavoidability
