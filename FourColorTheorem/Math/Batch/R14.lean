import FourColorTheorem.Math.Batch.Batch40_R14_Part1
import FourColorTheorem.Math.Batch.Batch41_R14_Part2
import FourColorTheorem.Math.Batch.Batch42_R14_Part3
import FourColorTheorem.Math.Batch.Batch43_R14_Part4
import FourColorTheorem.Math.Batch.Batch44_R14_Part5
import FourColorTheorem.Math.Batch.Batch45_R14_Part6
import FourColorTheorem.Math.Batch.Batch46_R14_Part7
import FourColorTheorem.Math.Batch.Batch47_R14_Part8
import FourColorTheorem.Math.Batch.Batch48_R14_Part9
import FourColorTheorem.Math.Batch.Batch49_R14_Part10
import FourColorTheorem.Math.Batch.Batch50_R14_Part11
import FourColorTheorem.Math.Batch.Batch51_R14_Part12
import FourColorTheorem.Math.Batch.Batch52_R14_Part13

namespace Math
namespace Batch

/-!
# Master In-Kernel Certificate: Ring Size 14

This module aggregates the in-kernel certification of all 26 D-reducible
configurations with ring size 14 from the RSST unavoidable set.

Every configuration below is proven directly by Lean 4's `native_decide`
reflection mechanism without external scripts or unproven axioms.
-/

/-- Total number of D-reducible configurations certified for ring size 14. -/
def certified_count_r14 : Nat := 26

/-- Index list of the 26 certified D-reducible configurations for ring size 14,
    composed directly from the 13 verified in-kernel batch modules. -/
def certified_indices_r14 : List Nat :=
  batch40_indices ++
  batch41_indices ++
  batch42_indices ++
  batch43_indices ++
  batch44_indices ++
  batch45_indices ++
  batch46_indices ++
  batch47_indices ++
  batch48_indices ++
  batch49_indices ++
  batch50_indices ++
  batch51_indices ++
  batch52_indices

theorem certified_count_r14_eq : certified_indices_r14.length = certified_count_r14 := by
  rfl

/-- All 13 Ring 14 D-reduction batch certificates combined into a single verifiable theorem. -/
theorem r14_batches_verified :
    checkRingBatch14 batch40_indices = true ∧
    checkRingBatch14 batch41_indices = true ∧
    checkRingBatch14 batch42_indices = true ∧
    checkRingBatch14 batch43_indices = true ∧
    checkRingBatch14 batch44_indices = true ∧
    checkRingBatch14 batch45_indices = true ∧
    checkRingBatch14 batch46_indices = true ∧
    checkRingBatch14 batch47_indices = true ∧
    checkRingBatch14 batch48_indices = true ∧
    checkRingBatch14 batch49_indices = true ∧
    checkRingBatch14 batch50_indices = true ∧
    checkRingBatch14 batch51_indices = true ∧
    checkRingBatch14 batch52_indices = true :=
  ⟨cert_batch40_r14, cert_batch41_r14, cert_batch42_r14, cert_batch43_r14,
   cert_batch44_r14, cert_batch45_r14, cert_batch46_r14, cert_batch47_r14,
   cert_batch48_r14, cert_batch49_r14, cert_batch50_r14, cert_batch51_r14,
   cert_batch52_r14⟩

end Batch
end Math
