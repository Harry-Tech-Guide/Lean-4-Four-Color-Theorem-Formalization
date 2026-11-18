module

/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
Released under Apache 2.0 license.
-/
public import FourColorTheorem.Math.Unavoidability.ConfGeomCertBase

@[expose] public section

/-!
# 633-Configuration Geometric Certificate Blocks 6–7 (Stage R.1)
-/

namespace Math.Unavoidability

open Math Math.Discharging GeomCert

private theorem row_6_0 : checkListZipGeom fcRow_6_0 rcRow_6_0 = true := rfl
private theorem row_6_1 : checkListZipGeom fcRow_6_1 rcRow_6_1 = true := rfl
private theorem row_6_2 : checkListZipGeom fcRow_6_2 rcRow_6_2 = true := rfl
private theorem row_6_3 : checkListZipGeom fcRow_6_3 rcRow_6_3 = true := rfl
private theorem row_6_4 : checkListZipGeom fcRow_6_4 rcRow_6_4 = true := rfl
private theorem row_6_5 : checkListZipGeom fcRow_6_5 rcRow_6_5 = true := rfl
private theorem row_6_6 : checkListZipGeom fcRow_6_6 rcRow_6_6 = true := rfl
private theorem row_6_7 : checkListZipGeom fcRow_6_7 rcRow_6_7 = true := rfl

private theorem row_7_0 : checkListZipGeom fcRow_7_0 rcRow_7_0 = true := rfl
private theorem row_7_1 : checkListZipGeom fcRow_7_1 rcRow_7_1 = true := rfl
private theorem row_7_2 : checkListZipGeom fcRow_7_2 rcRow_7_2 = true := rfl
private theorem row_7_3 : checkListZipGeom fcRow_7_3 rcRow_7_3 = true := rfl
private theorem row_7_4 : checkListZipGeom fcRow_7_4 rcRow_7_4 = true := rfl
private theorem row_7_5 : checkListZipGeom fcRow_7_5 rcRow_7_5 = true := rfl
private theorem row_7_6 : checkListZipGeom fcRow_7_6 rcRow_7_6 = true := rfl
private theorem row_7_7 : checkListZipGeom fcRow_7_7 rcRow_7_7 = true := rfl

theorem geom_blk_6 (r : Nat) (hr : r < 8) :
    checkListZipGeom
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

theorem geom_blk_7 (r : Nat) (hr : r < 8) :
    checkListZipGeom
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
