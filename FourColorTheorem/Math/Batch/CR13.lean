import FourColorTheorem.Math.Batch.CBatch26_R13_Part1
import FourColorTheorem.Math.Batch.CBatch27_R13_Part2
import FourColorTheorem.Math.Batch.CBatch28_R13_Part3
import FourColorTheorem.Math.Batch.CBatch29_R13_Part4
import FourColorTheorem.Math.Batch.CBatch30_R13_Part5
import FourColorTheorem.Math.Batch.CBatch31_R13_Part6
import FourColorTheorem.Math.Batch.CBatch32_R13_Part7
import FourColorTheorem.Math.Batch.CBatch33_R13_Part8
import FourColorTheorem.Math.Batch.CBatch34_R13_Part9
import FourColorTheorem.Math.Batch.CBatch35_R13_Part10
import FourColorTheorem.Math.Batch.CBatch36_R13_Part11
import FourColorTheorem.Math.Batch.CBatch37_R13_Part12
import FourColorTheorem.Math.Batch.CBatch38_R13_Part13
import FourColorTheorem.Math.Batch.CBatch39_R13_Part14
import FourColorTheorem.Math.Batch.CBatch40_R13_Part15
import FourColorTheorem.Math.Batch.CBatch41_R13_Part16
import FourColorTheorem.Math.Batch.CBatch42_R13_Part17
import FourColorTheorem.Math.Batch.CBatch43_R13_Part18
import FourColorTheorem.Math.Batch.CBatch44_R13_Part19
import FourColorTheorem.Math.Batch.CBatch45_R13_Part20
import FourColorTheorem.Math.Batch.CBatch46_R13_Part21
import FourColorTheorem.Math.Batch.CBatch47_R13_Part22
import FourColorTheorem.Math.Batch.CBatch48_R13_Part23
import FourColorTheorem.Math.Batch.CBatch49_R13_Part24

namespace Math
namespace Batch

/-!
# Master In-Kernel Certificate: C-Reducibility for Ring Size 13

This module aggregates the in-kernel certification of all 142 C-reducible
configurations with ring size 13 from the RSST unavoidable set.

Every configuration below is proven directly by Lean 4's `native_decide`
reflection mechanism without external scripts or unproven axioms.
-/

/-- Total number of C-reducible configurations certified for ring size 13. -/
def certified_count_cr13 : Nat := 142

/-- Index list of the 142 certified C-reducible configurations for ring size 13,
    composed directly from the 24 verified in-kernel batch modules. -/
def certified_indices_cr13 : List Nat :=
  cbatch26_indices ++
  cbatch27_indices ++
  cbatch28_indices ++
  cbatch29_indices ++
  cbatch30_indices ++
  cbatch31_indices ++
  cbatch32_indices ++
  cbatch33_indices ++
  cbatch34_indices ++
  cbatch35_indices ++
  cbatch36_indices ++
  cbatch37_indices ++
  cbatch38_indices ++
  cbatch39_indices ++
  cbatch40_indices ++
  cbatch41_indices ++
  cbatch42_indices ++
  cbatch43_indices ++
  cbatch44_indices ++
  cbatch45_indices ++
  cbatch46_indices ++
  cbatch47_indices ++
  cbatch48_indices ++
  cbatch49_indices

theorem certified_count_cr13_eq : certified_indices_cr13.length = certified_count_cr13 := by
  rfl

/-- All 24 Ring 13 C-reduction batch certificates combined into a single verifiable theorem. -/
theorem cr13_batches_verified :
    checkCRingBatch13 cbatch26_indices = true ∧
    checkCRingBatch13 cbatch27_indices = true ∧
    checkCRingBatch13 cbatch28_indices = true ∧
    checkCRingBatch13 cbatch29_indices = true ∧
    checkCRingBatch13 cbatch30_indices = true ∧
    checkCRingBatch13 cbatch31_indices = true ∧
    checkCRingBatch13 cbatch32_indices = true ∧
    checkCRingBatch13 cbatch33_indices = true ∧
    checkCRingBatch13 cbatch34_indices = true ∧
    checkCRingBatch13 cbatch35_indices = true ∧
    checkCRingBatch13 cbatch36_indices = true ∧
    checkCRingBatch13 cbatch37_indices = true ∧
    checkCRingBatch13 cbatch38_indices = true ∧
    checkCRingBatch13 cbatch39_indices = true ∧
    checkCRingBatch13 cbatch40_indices = true ∧
    checkCRingBatch13 cbatch41_indices = true ∧
    checkCRingBatch13 cbatch42_indices = true ∧
    checkCRingBatch13 cbatch43_indices = true ∧
    checkCRingBatch13 cbatch44_indices = true ∧
    checkCRingBatch13 cbatch45_indices = true ∧
    checkCRingBatch13 cbatch46_indices = true ∧
    checkCRingBatch13 cbatch47_indices = true ∧
    checkCRingBatch13 cbatch48_indices = true ∧
    checkCRingBatch13 cbatch49_indices = true :=
  ⟨cert_cbatch26_r13, cert_cbatch27_r13, cert_cbatch28_r13, cert_cbatch29_r13,
   cert_cbatch30_r13, cert_cbatch31_r13, cert_cbatch32_r13, cert_cbatch33_r13,
   cert_cbatch34_r13, cert_cbatch35_r13, cert_cbatch36_r13, cert_cbatch37_r13,
   cert_cbatch38_r13, cert_cbatch39_r13, cert_cbatch40_r13, cert_cbatch41_r13,
   cert_cbatch42_r13, cert_cbatch43_r13, cert_cbatch44_r13, cert_cbatch45_r13,
   cert_cbatch46_r13, cert_cbatch47_r13, cert_cbatch48_r13, cert_cbatch49_r13⟩

end Batch
end Math
