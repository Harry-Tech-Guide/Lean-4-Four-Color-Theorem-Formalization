module

/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
Released under Apache 2.0 license.
-/
public import FourColorTheorem.Math.Unavoidability.ConfGeomCertBase

@[expose] public section

/-!
# 633-Configuration Geometric Certificate Blocks 8–9 (Stage R.1)
-/

namespace Math.Unavoidability

open Math Math.Discharging GeomCert

private theorem row_8_0 : checkListZipGeom fcRow_8_0 rcRow_8_0 = true := rfl
private theorem row_8_1 : checkListZipGeom fcRow_8_1 rcRow_8_1 = true := rfl
private theorem row_8_2 : checkListZipGeom fcRow_8_2 rcRow_8_2 = true := rfl
private theorem row_8_3 : checkListZipGeom fcRow_8_3 rcRow_8_3 = true := rfl
private theorem row_8_4 : checkListZipGeom fcRow_8_4 rcRow_8_4 = true := rfl
private theorem row_8_5 : checkListZipGeom fcRow_8_5 rcRow_8_5 = true := rfl
private theorem row_8_6 : checkListZipGeom fcRow_8_6 rcRow_8_6 = true := rfl
private theorem row_8_7 : checkListZipGeom fcRow_8_7 rcRow_8_7 = true := rfl

private theorem row_9_0 : checkListZipGeom fcRow_9_0 rcRow_9_0 = true := rfl
private theorem row_9_1 : checkListZipGeom fcRow_9_1 rcRow_9_1 = true := rfl
private theorem row_9_2 : checkListZipGeom fcRow_9_2 rcRow_9_2 = true := rfl
private theorem row_9_3 : checkListZipGeom fcRow_9_3 rcRow_9_3 = true := rfl
private theorem row_9_4 : checkListZipGeom fcRow_9_4 rcRow_9_4 = true := rfl
private theorem row_9_5 : checkListZipGeom fcRow_9_5 rcRow_9_5 = true := rfl
private theorem row_9_6 : checkListZipGeom fcRow_9_6 rcRow_9_6 = true := rfl
private theorem row_9_7 : checkListZipGeom fcRow_9_7 rcRow_9_7 = true := rfl

theorem geom_blk_8 (r : Nat) (hr : r < 8) :
    checkListZipGeom
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

theorem geom_blk_9 (r : Nat) (hr : r < 8) :
    checkListZipGeom
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
