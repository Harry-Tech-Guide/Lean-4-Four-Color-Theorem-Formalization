module

/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
Released under Apache 2.0 license.
-/
public import FourColorTheorem.Math.Unavoidability.ConfGeomCertBase

@[expose] public section

/-!
# 633-Configuration Geometric Certificate Blocks 0–1 (Stage R.1)
-/

namespace Math.Unavoidability

open Math Math.Discharging GeomCert

private theorem row_0_0 : checkListZipGeom fcRow_0_0 rcRow_0_0 = true := rfl
private theorem row_0_1 : checkListZipGeom fcRow_0_1 rcRow_0_1 = true := rfl
private theorem row_0_2 : checkListZipGeom fcRow_0_2 rcRow_0_2 = true := rfl
private theorem row_0_3 : checkListZipGeom fcRow_0_3 rcRow_0_3 = true := rfl
private theorem row_0_4 : checkListZipGeom fcRow_0_4 rcRow_0_4 = true := rfl
private theorem row_0_5 : checkListZipGeom fcRow_0_5 rcRow_0_5 = true := rfl
private theorem row_0_6 : checkListZipGeom fcRow_0_6 rcRow_0_6 = true := rfl
private theorem row_0_7 : checkListZipGeom fcRow_0_7 rcRow_0_7 = true := rfl

private theorem row_1_0 : checkListZipGeom fcRow_1_0 rcRow_1_0 = true := rfl
private theorem row_1_1 : checkListZipGeom fcRow_1_1 rcRow_1_1 = true := rfl
private theorem row_1_2 : checkListZipGeom fcRow_1_2 rcRow_1_2 = true := rfl
private theorem row_1_3 : checkListZipGeom fcRow_1_3 rcRow_1_3 = true := rfl
private theorem row_1_4 : checkListZipGeom fcRow_1_4 rcRow_1_4 = true := rfl
private theorem row_1_5 : checkListZipGeom fcRow_1_5 rcRow_1_5 = true := rfl
private theorem row_1_6 : checkListZipGeom fcRow_1_6 rcRow_1_6 = true := rfl
private theorem row_1_7 : checkListZipGeom fcRow_1_7 rcRow_1_7 = true := rfl

theorem geom_blk_0 (r : Nat) (hr : r < 8) :
    checkListZipGeom
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

theorem geom_blk_1 (r : Nat) (hr : r < 8) :
    checkListZipGeom
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
