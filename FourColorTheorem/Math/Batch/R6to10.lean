import FourColorTheorem.Math.Batch.Runner
import FourColorTheorem.Math.Batch.Batch01_R6to9
import FourColorTheorem.Math.Batch.Batch02_R10_Part1
import FourColorTheorem.Math.Batch.Batch03_R10_Part2

namespace Math
namespace Batch

open FastReducer

def batch01_r6_indices : List Nat := [0]
def batch01_r7_indices : List Nat := [1]
def batch01_r8_indices : List Nat := [2, 4, 7, 23]
def batch01_r9_indices : List Nat := [5, 6, 11, 24, 26, 37, 323]
def batch02_r10_indices : List Nat := [8, 9, 12, 13, 18, 27, 29, 30, 32, 36, 44]
def batch03_r10_indices : List Nat := [45, 47, 76, 110, 112, 324, 325, 328, 343, 566]

def certified_count_r6to10 : Nat := 34
def certified_indices_r6to10 : List Nat :=
  batch01_r6_indices ++ batch01_r7_indices ++ batch01_r8_indices ++
  batch01_r9_indices ++ batch02_r10_indices ++ batch03_r10_indices

theorem certified_count_eq : certified_indices_r6to10.length = certified_count_r6to10 := by rfl

theorem cert_batch01_r6 : checkRingBatch 6 batch01_r6_indices = true := by
  dsimp only [batch01_r6_indices, checkRingBatch, List.all]; rw [cert_config_0_d_red]; rfl
theorem cert_batch01_r7 : checkRingBatch 7 batch01_r7_indices = true := by
  dsimp only [batch01_r7_indices, checkRingBatch, List.all]; rw [cert_config_1_d_red]; rfl
theorem cert_batch01_r8 : checkRingBatch 8 batch01_r8_indices = true := by
  dsimp only [batch01_r8_indices, checkRingBatch, List.all]
  rw [cert_config_2_d_red, cert_config_4_d_red, cert_config_7_d_red, cert_config_23_d_red]; rfl
theorem cert_batch01_r9 : checkRingBatch 9 batch01_r9_indices = true := by
  dsimp only [batch01_r9_indices, checkRingBatch, List.all]
  rw [cert_config_5_d_red, cert_config_6_d_red, cert_config_11_d_red, cert_config_24_d_red, cert_config_26_d_red, cert_config_37_d_red, cert_config_323_d_red]; rfl
theorem cert_batch02_r10 : checkRingBatch 10 batch02_r10_indices = true := by
  dsimp only [batch02_r10_indices, checkRingBatch, List.all]
  rw [cert_config_8_d_red, cert_config_9_d_red, cert_config_12_d_red, cert_config_13_d_red, cert_config_18_d_red, cert_config_27_d_red, cert_config_29_d_red, cert_config_30_d_red, cert_config_32_d_red, cert_config_36_d_red, cert_config_44_d_red]; rfl
theorem cert_batch03_r10 : checkRingBatch 10 batch03_r10_indices = true := by
  dsimp only [batch03_r10_indices, checkRingBatch, List.all]
  rw [cert_config_45_d_red, cert_config_47_d_red, cert_config_76_d_red, cert_config_110_d_red, cert_config_112_d_red, cert_config_324_d_red, cert_config_325_d_red, cert_config_328_d_red, cert_config_343_d_red, cert_config_566_d_red]; rfl

theorem r6to10_batches_verified :
    checkRingBatch 6 batch01_r6_indices = true ∧
    checkRingBatch 7 batch01_r7_indices = true ∧
    checkRingBatch 8 batch01_r8_indices = true ∧
    checkRingBatch 9 batch01_r9_indices = true ∧
    checkRingBatch 10 batch02_r10_indices = true ∧
    checkRingBatch 10 batch03_r10_indices = true :=
  ⟨cert_batch01_r6, cert_batch01_r7, cert_batch01_r8, cert_batch01_r9, cert_batch02_r10, cert_batch03_r10⟩

end Batch
end Math
