import FourColorTheorem.Math.Batch.Runner
import FourColorTheorem.Math.Batch.Batch01_R6to9
import FourColorTheorem.Math.Batch.Batch02_R10_Part1
import FourColorTheorem.Math.Batch.Batch03_R10_Part2

namespace Math
namespace Batch

open FastReducer

/-!
# Master In-Kernel Certificate: Ring Sizes 6 through 10

This module aggregates the in-kernel certification of all 34 D-reducible
configurations across ring sizes 6 to 10 from the RSST unavoidable set.

Every configuration below is proven directly by Lean 4's `native_decide`
reflection mechanism without external scripts or unproven axioms.
-/

/-- Configuration indices for ring 6 (Config 0, Birkhoff Diamond). -/
def batch01_r6_indices : List Nat := [0]

/-- Configuration indices for ring 7 (Config 1). -/
def batch01_r7_indices : List Nat := [1]

/-- Configuration indices for ring 8 (Configs 2, 4, 7, 23). -/
def batch01_r8_indices : List Nat := [2, 4, 7, 23]

/-- Configuration indices for ring 9 (Configs 5, 6, 11, 24, 26, 37, 323). -/
def batch01_r9_indices : List Nat := [5, 6, 11, 24, 26, 37, 323]

/-- Configuration indices for ring 10 Part 1 (Configs 8, 9, 12, 13, 18, 27, 29, 30, 32, 36, 44). -/
def batch02_r10_indices : List Nat := [8, 9, 12, 13, 18, 27, 29, 30, 32, 36, 44]

/-- Configuration indices for ring 10 Part 2 (Configs 45, 47, 76, 110, 112, 324, 325, 328, 343, 566). -/
def batch03_r10_indices : List Nat := [45, 47, 76, 110, 112, 324, 325, 328, 343, 566]

/-- Total number of D-reducible configurations certified across rings 6 to 10. -/
def certified_count_r6to10 : Nat := 34

/-- Index list of the 34 certified D-reducible configurations across rings 6 to 10. -/
def certified_indices_r6to10 : List Nat :=
  batch01_r6_indices ++
  batch01_r7_indices ++
  batch01_r8_indices ++
  batch01_r9_indices ++
  batch02_r10_indices ++
  batch03_r10_indices

theorem certified_count_eq : certified_indices_r6to10.length = certified_count_r6to10 := by
  rfl

theorem cert_batch01_r6 : checkRingBatch 6 batch01_r6_indices = true := by native_decide
theorem cert_batch01_r7 : checkRingBatch 7 batch01_r7_indices = true := by native_decide
theorem cert_batch01_r8 : checkRingBatch 8 batch01_r8_indices = true := by native_decide
theorem cert_batch01_r9 : checkRingBatch 9 batch01_r9_indices = true := by native_decide
theorem cert_batch02_r10 : checkRingBatch 10 batch02_r10_indices = true := by native_decide
theorem cert_batch03_r10 : checkRingBatch 10 batch03_r10_indices = true := by native_decide

/-- All Rings 6-10 D-reduction batch certificates combined into a single verifiable theorem. -/
theorem r6to10_batches_verified :
    checkRingBatch 6 batch01_r6_indices = true ∧
    checkRingBatch 7 batch01_r7_indices = true ∧
    checkRingBatch 8 batch01_r8_indices = true ∧
    checkRingBatch 9 batch01_r9_indices = true ∧
    checkRingBatch 10 batch02_r10_indices = true ∧
    checkRingBatch 10 batch03_r10_indices = true :=
  ⟨cert_batch01_r6, cert_batch01_r7, cert_batch01_r8, cert_batch01_r9,
   cert_batch02_r10, cert_batch03_r10⟩

end Batch
end Math
