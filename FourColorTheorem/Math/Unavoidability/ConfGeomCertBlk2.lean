module

/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
Released under Apache 2.0 license.
-/
public import FourColorTheorem.Math.Unavoidability.ConfGeomCertBase

@[expose] public section

/-!
# 633-Configuration Geometric Certificate Blocks 4–5 (Stage R.1)
-/

namespace Math.Unavoidability

open Math Math.Discharging GeomCert

private theorem row_4_0 : checkListZipGeom fcRow_4_0 rcRow_4_0 = true := rfl
private theorem row_4_1 : checkListZipGeom fcRow_4_1 rcRow_4_1 = true := rfl
private theorem row_4_2 : checkListZipGeom fcRow_4_2 rcRow_4_2 = true := rfl
private theorem row_4_3 : checkListZipGeom fcRow_4_3 rcRow_4_3 = true := rfl
private theorem row_4_4 : checkListZipGeom fcRow_4_4 rcRow_4_4 = true := rfl
private theorem row_4_5 : checkListZipGeom fcRow_4_5 rcRow_4_5 = true := rfl
private theorem row_4_6 : checkListZipGeom fcRow_4_6 rcRow_4_6 = true := rfl
private theorem row_4_7 : checkListZipGeom fcRow_4_7 rcRow_4_7 = true := rfl

private theorem row_5_0 : checkListZipGeom fcRow_5_0 rcRow_5_0 = true := rfl
private theorem row_5_1 : checkListZipGeom fcRow_5_1 rcRow_5_1 = true := rfl
private theorem row_5_2 : checkListZipGeom fcRow_5_2 rcRow_5_2 = true := rfl
private theorem row_5_3 : checkListZipGeom fcRow_5_3 rcRow_5_3 = true := rfl
private theorem row_5_4 : checkListZipGeom fcRow_5_4 rcRow_5_4 = true := rfl
private theorem row_5_5 : checkListZipGeom fcRow_5_5 rcRow_5_5 = true := rfl
private theorem row_5_6 : checkListZipGeom fcRow_5_6 rcRow_5_6 = true := rfl
private theorem row_5_7 : checkListZipGeom fcRow_5_7 rcRow_5_7 = true := rfl

theorem geom_blk_4 (r : Nat) (hr : r < 8) :
    checkListZipGeom
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

theorem geom_blk_5 (r : Nat) (hr : r < 8) :
    checkListZipGeom
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
