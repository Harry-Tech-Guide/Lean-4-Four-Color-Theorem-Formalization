import FourColorTheorem.Math.Batch.CBatch50_R14_Part1
import FourColorTheorem.Math.Batch.CBatch51_R14_Part2
import FourColorTheorem.Math.Batch.CBatch52_R14_Part3
import FourColorTheorem.Math.Batch.CBatch53_R14_Part4
import FourColorTheorem.Math.Batch.CBatch54_R14_Part5
import FourColorTheorem.Math.Batch.CBatch55_R14_Part6
import FourColorTheorem.Math.Batch.CBatch56_R14_Part7
import FourColorTheorem.Math.Batch.CBatch57_R14_Part8
import FourColorTheorem.Math.Batch.CBatch58_R14_Part9
import FourColorTheorem.Math.Batch.CBatch59_R14_Part10
import FourColorTheorem.Math.Batch.CBatch60_R14_Part11
import FourColorTheorem.Math.Batch.CBatch61_R14_Part12
import FourColorTheorem.Math.Batch.CBatch62_R14_Part13
import FourColorTheorem.Math.Batch.CBatch63_R14_Part14
import FourColorTheorem.Math.Batch.CBatch64_R14_Part15
import FourColorTheorem.Math.Batch.CBatch65_R14_Part16
import FourColorTheorem.Math.Batch.CBatch66_R14_Part17
import FourColorTheorem.Math.Batch.CBatch67_R14_Part18
import FourColorTheorem.Math.Batch.CBatch68_R14_Part19
import FourColorTheorem.Math.Batch.CBatch69_R14_Part20
import FourColorTheorem.Math.Batch.CBatch70_R14_Part21
import FourColorTheorem.Math.Batch.CBatch71_R14_Part22
import FourColorTheorem.Math.Batch.CBatch72_R14_Part23
import FourColorTheorem.Math.Batch.CBatch73_R14_Part24
import FourColorTheorem.Math.Batch.CBatch74_R14_Part25
import FourColorTheorem.Math.Batch.CBatch75_R14_Part26
import FourColorTheorem.Math.Batch.CBatch76_R14_Part27
import FourColorTheorem.Math.Batch.CBatch77_R14_Part28
import FourColorTheorem.Math.Batch.CBatch78_R14_Part29
import FourColorTheorem.Math.Batch.CBatch79_R14_Part30
import FourColorTheorem.Math.Batch.CBatch80_R14_Part31
import FourColorTheorem.Math.Batch.CBatch81_R14_Part32
import FourColorTheorem.Math.Batch.CBatch82_R14_Part33
import FourColorTheorem.Math.Batch.CBatch83_R14_Part34
import FourColorTheorem.Math.Batch.CBatch84_R14_Part35
import FourColorTheorem.Math.Batch.CBatch85_R14_Part36
import FourColorTheorem.Math.Batch.CBatch86_R14_Part37

namespace Math
namespace Batch

/-!
# Master In-Kernel Certificate: C-Reducibility for Ring Size 14

This module aggregates the in-kernel certification of all 111 C-reducible
configurations with ring size 14 from the RSST unavoidable set.

Every configuration below is proven directly by Lean 4's `native_decide`
reflection mechanism without external scripts or unproven axioms.
-/

/-- Total number of C-reducible configurations certified for ring size 14. -/
def certified_count_cr14 : Nat := 111

/-- Index list of the 111 certified C-reducible configurations for ring size 14,
    composed directly from the 37 verified in-kernel batch modules. -/
def certified_indices_cr14 : List Nat :=
  cbatch50_indices ++
  cbatch51_indices ++
  cbatch52_indices ++
  cbatch53_indices ++
  cbatch54_indices ++
  cbatch55_indices ++
  cbatch56_indices ++
  cbatch57_indices ++
  cbatch58_indices ++
  cbatch59_indices ++
  cbatch60_indices ++
  cbatch61_indices ++
  cbatch62_indices ++
  cbatch63_indices ++
  cbatch64_indices ++
  cbatch65_indices ++
  cbatch66_indices ++
  cbatch67_indices ++
  cbatch68_indices ++
  cbatch69_indices ++
  cbatch70_indices ++
  cbatch71_indices ++
  cbatch72_indices ++
  cbatch73_indices ++
  cbatch74_indices ++
  cbatch75_indices ++
  cbatch76_indices ++
  cbatch77_indices ++
  cbatch78_indices ++
  cbatch79_indices ++
  cbatch80_indices ++
  cbatch81_indices ++
  cbatch82_indices ++
  cbatch83_indices ++
  cbatch84_indices ++
  cbatch85_indices ++
  cbatch86_indices

theorem certified_count_cr14_eq : certified_indices_cr14.length = certified_count_cr14 := by
  rfl

/-- All 37 Ring 14 C-reduction batch certificates combined into a single verifiable theorem. -/
theorem cr14_batches_verified :
    checkCRingBatch14 cbatch50_indices = true ∧
    checkCRingBatch14 cbatch51_indices = true ∧
    checkCRingBatch14 cbatch52_indices = true ∧
    checkCRingBatch14 cbatch53_indices = true ∧
    checkCRingBatch14 cbatch54_indices = true ∧
    checkCRingBatch14 cbatch55_indices = true ∧
    checkCRingBatch14 cbatch56_indices = true ∧
    checkCRingBatch14 cbatch57_indices = true ∧
    checkCRingBatch14 cbatch58_indices = true ∧
    checkCRingBatch14 cbatch59_indices = true ∧
    checkCRingBatch14 cbatch60_indices = true ∧
    checkCRingBatch14 cbatch61_indices = true ∧
    checkCRingBatch14 cbatch62_indices = true ∧
    checkCRingBatch14 cbatch63_indices = true ∧
    checkCRingBatch14 cbatch64_indices = true ∧
    checkCRingBatch14 cbatch65_indices = true ∧
    checkCRingBatch14 cbatch66_indices = true ∧
    checkCRingBatch14 cbatch67_indices = true ∧
    checkCRingBatch14 cbatch68_indices = true ∧
    checkCRingBatch14 cbatch69_indices = true ∧
    checkCRingBatch14 cbatch70_indices = true ∧
    checkCRingBatch14 cbatch71_indices = true ∧
    checkCRingBatch14 cbatch72_indices = true ∧
    checkCRingBatch14 cbatch73_indices = true ∧
    checkCRingBatch14 cbatch74_indices = true ∧
    checkCRingBatch14 cbatch75_indices = true ∧
    checkCRingBatch14 cbatch76_indices = true ∧
    checkCRingBatch14 cbatch77_indices = true ∧
    checkCRingBatch14 cbatch78_indices = true ∧
    checkCRingBatch14 cbatch79_indices = true ∧
    checkCRingBatch14 cbatch80_indices = true ∧
    checkCRingBatch14 cbatch81_indices = true ∧
    checkCRingBatch14 cbatch82_indices = true ∧
    checkCRingBatch14 cbatch83_indices = true ∧
    checkCRingBatch14 cbatch84_indices = true ∧
    checkCRingBatch14 cbatch85_indices = true ∧
    checkCRingBatch14 cbatch86_indices = true :=
  ⟨cert_cbatch50_r14, cert_cbatch51_r14, cert_cbatch52_r14, cert_cbatch53_r14,
   cert_cbatch54_r14, cert_cbatch55_r14, cert_cbatch56_r14, cert_cbatch57_r14,
   cert_cbatch58_r14, cert_cbatch59_r14, cert_cbatch60_r14, cert_cbatch61_r14,
   cert_cbatch62_r14, cert_cbatch63_r14, cert_cbatch64_r14, cert_cbatch65_r14,
   cert_cbatch66_r14, cert_cbatch67_r14, cert_cbatch68_r14, cert_cbatch69_r14,
   cert_cbatch70_r14, cert_cbatch71_r14, cert_cbatch72_r14, cert_cbatch73_r14,
   cert_cbatch74_r14, cert_cbatch75_r14, cert_cbatch76_r14, cert_cbatch77_r14,
   cert_cbatch78_r14, cert_cbatch79_r14, cert_cbatch80_r14, cert_cbatch81_r14,
   cert_cbatch82_r14, cert_cbatch83_r14, cert_cbatch84_r14, cert_cbatch85_r14,
   cert_cbatch86_r14⟩

end Batch
end Math
