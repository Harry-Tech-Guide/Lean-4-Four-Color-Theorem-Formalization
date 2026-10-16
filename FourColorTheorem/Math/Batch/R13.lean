import FourColorTheorem.Math.Batch.Batch27_R13_Part1
import FourColorTheorem.Math.Batch.Batch28_R13_Part2
import FourColorTheorem.Math.Batch.Batch29_R13_Part3
import FourColorTheorem.Math.Batch.Batch30_R13_Part4
import FourColorTheorem.Math.Batch.Batch31_R13_Part5
import FourColorTheorem.Math.Batch.Batch32_R13_Part6
import FourColorTheorem.Math.Batch.Batch33_R13_Part7
import FourColorTheorem.Math.Batch.Batch34_R13_Part8
import FourColorTheorem.Math.Batch.Batch35_R13_Part9
import FourColorTheorem.Math.Batch.Batch36_R13_Part10
import FourColorTheorem.Math.Batch.Batch37_R13_Part11
import FourColorTheorem.Math.Batch.Batch38_R13_Part12
import FourColorTheorem.Math.Batch.Batch39_R13_Part13

namespace Math
namespace Batch

/-!
# Master In-Kernel Certificate: Ring Size 13

This module aggregates the in-kernel certification of all 52 D-reducible
configurations with ring size 13 from the RSST unavoidable set.
-/

/-- Total number of D-reducible configurations certified for ring size 13. -/
def certified_count_r13 : Nat := 52

/-- Index list of the 52 certified D-reducible configurations for ring size 13,
    composed directly from the 13 verified in-kernel batch modules. -/
def certified_indices_r13 : List Nat :=
  batch27_indices ++
  batch28_indices ++
  batch29_indices ++
  batch30_indices ++
  batch31_indices ++
  batch32_indices ++
  batch33_indices ++
  batch34_indices ++
  batch35_indices ++
  batch36_indices ++
  batch37_indices ++
  batch38_indices ++
  batch39_indices

theorem certified_count_r13_eq : certified_indices_r13.length = certified_count_r13 := by
  rfl

/-- All 13 Ring 13 D-reduction batch certificates combined into a single verifiable theorem. -/
theorem r13_batches_verified :
    checkRingBatch13 batch27_indices = true ∧
    checkRingBatch13 batch28_indices = true ∧
    checkRingBatch13 batch29_indices = true ∧
    checkRingBatch13 batch30_indices = true ∧
    checkRingBatch13 batch31_indices = true ∧
    checkRingBatch13 batch32_indices = true ∧
    checkRingBatch13 batch33_indices = true ∧
    checkRingBatch13 batch34_indices = true ∧
    checkRingBatch13 batch35_indices = true ∧
    checkRingBatch13 batch36_indices = true ∧
    checkRingBatch13 batch37_indices = true ∧
    checkRingBatch13 batch38_indices = true ∧
    checkRingBatch13 batch39_indices = true :=
  ⟨cert_batch27_r13, cert_batch28_r13, cert_batch29_r13, cert_batch30_r13,
   cert_batch31_r13, cert_batch32_r13, cert_batch33_r13, cert_batch34_r13,
   cert_batch35_r13, cert_batch36_r13, cert_batch37_r13, cert_batch38_r13,
   cert_batch39_r13⟩

end Batch
end Math
