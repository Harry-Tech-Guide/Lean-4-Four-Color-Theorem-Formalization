module

/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
Released under Apache 2.0 license.
-/
public import FourColorTheorem.Math.Unavoidability.FastConfEquivData

@[expose] public section

/-!
# 633-Configuration `FastConf` ↔ `RConf` Certificate Block 1
-/

namespace Math.Unavoidability

open Math Math.Discharging

private theorem row_1_0 : checkListZipPrefix fcRow_1_0 rcRow_1_0 = true := rfl
private theorem row_1_1 : checkListZipPrefix fcRow_1_1 rcRow_1_1 = true := rfl
private theorem row_1_2 : checkListZipPrefix fcRow_1_2 rcRow_1_2 = true := rfl
private theorem row_1_3 : checkListZipPrefix fcRow_1_3 rcRow_1_3 = true := rfl
private theorem row_1_4 : checkListZipPrefix fcRow_1_4 rcRow_1_4 = true := rfl
private theorem row_1_5 : checkListZipPrefix fcRow_1_5 rcRow_1_5 = true := rfl
private theorem row_1_6 : checkListZipPrefix fcRow_1_6 rcRow_1_6 = true := rfl
private theorem row_1_7 : checkListZipPrefix fcRow_1_7 rcRow_1_7 = true := rfl

theorem equiv_blk_1 (r : Nat) (hr : r < 8) :
    checkListZipPrefix
      (fcBlk_1[r]'(by rw [fcBlk_1_len]; exact hr))
      (rcBlk_1[r]'(by rw [rcBlk_1_len]; exact hr)) = true := by
  match r with
  | 0 => exact row_1_0
  | 1 => exact row_1_1
  | 2 => exact row_1_2
  | 3 => exact row_1_3
  | 4 => exact row_1_4
  | 5 => exact row_1_5
  | 6 => exact row_1_6
  | 7 => exact row_1_7
  | _ + 8 => omega

end Math.Unavoidability
