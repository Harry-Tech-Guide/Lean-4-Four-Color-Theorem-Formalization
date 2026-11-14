/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
Released under Apache 2.0 license.
-/
import FourColorTheorem.Math.Unavoidability.ConfGeomCertBase

/-!
# 633-Configuration Geometric Certificate Blocks 2–3 (Stage R.1)
-/

namespace Math.Unavoidability

open Math Math.Discharging GeomCert

private theorem row_2_0 : checkListZipGeom fcRow_2_0 rcRow_2_0 = true := rfl
private theorem row_2_1 : checkListZipGeom fcRow_2_1 rcRow_2_1 = true := rfl
private theorem row_2_2 : checkListZipGeom fcRow_2_2 rcRow_2_2 = true := rfl
private theorem row_2_3 : checkListZipGeom fcRow_2_3 rcRow_2_3 = true := rfl
private theorem row_2_4 : checkListZipGeom fcRow_2_4 rcRow_2_4 = true := rfl
private theorem row_2_5 : checkListZipGeom fcRow_2_5 rcRow_2_5 = true := rfl
private theorem row_2_6 : checkListZipGeom fcRow_2_6 rcRow_2_6 = true := rfl
private theorem row_2_7 : checkListZipGeom fcRow_2_7 rcRow_2_7 = true := rfl

private theorem row_3_0 : checkListZipGeom fcRow_3_0 rcRow_3_0 = true := rfl
private theorem row_3_1 : checkListZipGeom fcRow_3_1 rcRow_3_1 = true := rfl
private theorem row_3_2 : checkListZipGeom fcRow_3_2 rcRow_3_2 = true := rfl
private theorem row_3_3 : checkListZipGeom fcRow_3_3 rcRow_3_3 = true := rfl
private theorem row_3_4 : checkListZipGeom fcRow_3_4 rcRow_3_4 = true := rfl
private theorem row_3_5 : checkListZipGeom fcRow_3_5 rcRow_3_5 = true := rfl
private theorem row_3_6 : checkListZipGeom fcRow_3_6 rcRow_3_6 = true := rfl
private theorem row_3_7 : checkListZipGeom fcRow_3_7 rcRow_3_7 = true := rfl

theorem geom_blk_2 (r : Nat) (hr : r < 8) :
    checkListZipGeom
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

theorem geom_blk_3 (r : Nat) (hr : r < 8) :
    checkListZipGeom
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
