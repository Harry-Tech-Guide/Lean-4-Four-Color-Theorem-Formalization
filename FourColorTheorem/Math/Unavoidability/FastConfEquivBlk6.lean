module

/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
Released under Apache 2.0 license.
-/
public import FourColorTheorem.Math.Unavoidability.FastConfEquivData

@[expose] public section

/-!
# 633-Configuration `FastConf` ↔ `RConf` Certificate Block 6
-/

namespace Math.Unavoidability

open Math Math.Discharging

private theorem row_6_0 : checkListZipPrefix fcRow_6_0 rcRow_6_0 = true := rfl
private theorem row_6_1 : checkListZipPrefix fcRow_6_1 rcRow_6_1 = true := rfl
private theorem row_6_2 : checkListZipPrefix fcRow_6_2 rcRow_6_2 = true := rfl
private theorem row_6_3 : checkListZipPrefix fcRow_6_3 rcRow_6_3 = true := rfl
private theorem row_6_4 : checkListZipPrefix fcRow_6_4 rcRow_6_4 = true := rfl
private theorem row_6_5 : checkListZipPrefix fcRow_6_5 rcRow_6_5 = true := rfl
private theorem row_6_6 : checkListZipPrefix fcRow_6_6 rcRow_6_6 = true := rfl
private theorem row_6_7 : checkListZipPrefix fcRow_6_7 rcRow_6_7 = true := rfl

theorem equiv_blk_6 (r : Nat) (hr : r < 8) :
    checkListZipPrefix
      (fcBlk_6[r]'(by rw [fcBlk_6_len]; exact hr))
      (rcBlk_6[r]'(by rw [rcBlk_6_len]; exact hr)) = true := by
  match r with
  | 0 => exact row_6_0
  | 1 => exact row_6_1
  | 2 => exact row_6_2
  | 3 => exact row_6_3
  | 4 => exact row_6_4
  | 5 => exact row_6_5
  | 6 => exact row_6_6
  | 7 => exact row_6_7
  | _ + 8 => omega

end Math.Unavoidability
