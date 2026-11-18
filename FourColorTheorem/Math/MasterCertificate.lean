module

public import FourColorTheorem.Math.Batch.R6to10
public import FourColorTheorem.Math.Batch.R11
public import FourColorTheorem.Math.Batch.R12
public import FourColorTheorem.Math.Batch.R13
public import FourColorTheorem.Math.Batch.R14
public import FourColorTheorem.Math.Batch.CR8to10
public import FourColorTheorem.Math.Batch.CR11
public import FourColorTheorem.Math.Batch.CR12
public import FourColorTheorem.Math.Batch.CR13
public import FourColorTheorem.Math.Batch.CR14
public import FourColorTheorem.Math.U633Parser
public import FourColorTheorem.Math.Reducibility
public import FourColorTheorem.Math.Soundness.DReduce
public import FourColorTheorem.Math.Soundness.CReduce
public import FourColorTheorem.Math.Soundness.StructuralVerification
public import FourColorTheorem.Math.CheckerSoundness.IterationElimination
public import FourColorTheorem.Math.KernelSoundness.KernelBridgeProof

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace MasterCertificate

open FastReducer
open Soundness
open Batch

/-!
# Master RSST Reducibility Certificate Aggregator

This module aggregates all 138 in-kernel batch certificate files covering
the entire Robertson-Sanders-Seymour-Thomas canonical unavoidable set:
- 52 D-reducibility batch modules (249 configurations across rings 6–14)
- 86 C-reducibility batch modules (384 configurations across rings 8–14)
Total: 633 configurations verified directly in the Lean 4 kernel via `kernel reduction`.

This module proves that all 633 configurations from `theUnavoidableSet` are
certified, and provides the explicit RSST certificate soundness bridge.
-/

/-- Master index list of all 249 D-reducible configurations. -/
def certified_d_indices : List Nat :=
  Batch.certified_indices_r6to10 ++
  Batch.certified_indices_r11 ++
  Batch.certified_indices_r12 ++
  Batch.certified_indices_r13 ++
  Batch.certified_indices_r14

/-- Master index list of all 384 C-reducible configurations. -/
def certified_c_indices : List Nat :=
  Batch.certified_indices_cr8to10 ++
  Batch.certified_indices_cr11 ++
  Batch.certified_indices_cr12 ++
  Batch.certified_indices_cr13 ++
  Batch.certified_indices_cr14

/-- All 633 certified configuration indices combined. -/
def all_certified_indices : List Nat :=
  certified_d_indices ++ certified_c_indices

set_option maxRecDepth 500000 in
/-- Exact count of certified D-reducible configurations: 249. -/
theorem total_d_count : certified_d_indices.length = 249 := by rfl

set_option maxRecDepth 500000 in
/-- Exact count of certified C-reducible configurations: 384. -/
theorem total_c_count : certified_c_indices.length = 384 := by rfl

set_option maxRecDepth 500000 in
/-- Exact count of all certified configurations: 633. -/
theorem total_certified_count : all_certified_indices.length = 633 := by rfl

/-- The canonical RSST dataset contains exactly 633 configurations. -/
theorem unavoidable_size_eq : theUnavoidableSet.size = 633 :=
  Math.unavoidable_size_eq

/-- Master In-Kernel Certificate Suite Proposition:
    Explicitly states that all in-kernel reflection batch theorems across ALL 10 ring suites
    (R6to10, R11, R12, R13, R14, CR8to10, CR11, CR12, CR13, CR14) — comprising all 138 batch
    reflection files covering all 633 configurations — are verified directly by Lean 4's kernel reduction. -/
def MasterSuiteVerifiedProp : Prop :=
    (Batch.checkRingBatch 6 Batch.batch01_r6_indices = true ∧
     Batch.checkRingBatch 7 Batch.batch01_r7_indices = true ∧
     Batch.checkRingBatch 8 Batch.batch01_r8_indices = true ∧
     Batch.checkRingBatch 9 Batch.batch01_r9_indices = true ∧
     Batch.checkRingBatch 10 Batch.batch02_r10_indices = true ∧
     Batch.checkRingBatch 10 Batch.batch03_r10_indices = true) ∧
    (Batch.checkRingBatch 11 Batch.batch04_indices = true ∧
     Batch.checkRingBatch 11 Batch.batch05_indices = true ∧
     Batch.checkRingBatch 11 Batch.batch06_indices = true ∧
     Batch.checkRingBatch 11 Batch.batch07_indices = true ∧
     Batch.checkRingBatch 11 Batch.batch08_indices = true ∧
     Batch.checkRingBatch 11 Batch.batch09_indices = true ∧
     Batch.checkRingBatch 11 Batch.batch10_indices = true) ∧
    (Batch.checkRingBatch 12 Batch.batch11_indices = true ∧
     Batch.checkRingBatch 12 Batch.batch12_indices = true ∧
     Batch.checkRingBatch 12 Batch.batch13_indices = true ∧
     Batch.checkRingBatch 12 Batch.batch14_indices = true ∧
     Batch.checkRingBatch 12 Batch.batch15_indices = true ∧
     Batch.checkRingBatch 12 Batch.batch16_indices = true ∧
     Batch.checkRingBatch 12 Batch.batch17_indices = true ∧
     Batch.checkRingBatch 12 Batch.batch18_indices = true ∧
     Batch.checkRingBatch 12 Batch.batch19_indices = true ∧
     Batch.checkRingBatch 12 Batch.batch20_indices = true ∧
     Batch.checkRingBatch 12 Batch.batch21_indices = true ∧
     Batch.checkRingBatch 12 Batch.batch22_indices = true ∧
     Batch.checkRingBatch 12 Batch.batch23_indices = true ∧
     Batch.checkRingBatch 12 Batch.batch24_indices = true ∧
     Batch.checkRingBatch 12 Batch.batch25_indices = true ∧
     Batch.checkRingBatch 12 Batch.batch26_indices = true) ∧
    (Batch.checkRingBatch13 Batch.batch27_indices = true ∧
     Batch.checkRingBatch13 Batch.batch28_indices = true ∧
     Batch.checkRingBatch13 Batch.batch29_indices = true ∧
     Batch.checkRingBatch13 Batch.batch30_indices = true ∧
     Batch.checkRingBatch13 Batch.batch31_indices = true ∧
     Batch.checkRingBatch13 Batch.batch32_indices = true ∧
     Batch.checkRingBatch13 Batch.batch33_indices = true ∧
     Batch.checkRingBatch13 Batch.batch34_indices = true ∧
     Batch.checkRingBatch13 Batch.batch35_indices = true ∧
     Batch.checkRingBatch13 Batch.batch36_indices = true ∧
     Batch.checkRingBatch13 Batch.batch37_indices = true ∧
     Batch.checkRingBatch13 Batch.batch38_indices = true ∧
     Batch.checkRingBatch13 Batch.batch39_indices = true) ∧
    (Batch.checkRingBatch14 Batch.batch40_indices = true ∧
     Batch.checkRingBatch14 Batch.batch41_indices = true ∧
     Batch.checkRingBatch14 Batch.batch42_indices = true ∧
     Batch.checkRingBatch14 Batch.batch43_indices = true ∧
     Batch.checkRingBatch14 Batch.batch44_indices = true ∧
     Batch.checkRingBatch14 Batch.batch45_indices = true ∧
     Batch.checkRingBatch14 Batch.batch46_indices = true ∧
     Batch.checkRingBatch14 Batch.batch47_indices = true ∧
     Batch.checkRingBatch14 Batch.batch48_indices = true ∧
     Batch.checkRingBatch14 Batch.batch49_indices = true ∧
     Batch.checkRingBatch14 Batch.batch50_indices = true ∧
     Batch.checkRingBatch14 Batch.batch51_indices = true ∧
     Batch.checkRingBatch14 Batch.batch52_indices = true) ∧
    (Batch.checkCRingBatch 8 Batch.cbatch01_indices = true ∧
     Batch.checkCRingBatch 9 Batch.cbatch02_indices = true ∧
     Batch.checkCRingBatch 10 Batch.cbatch03_indices = true ∧
     Batch.checkCRingBatch 10 Batch.cbatch04_indices = true) ∧
    (Batch.checkCRingBatch 11 Batch.cbatch05_indices = true ∧
     Batch.checkCRingBatch 11 Batch.cbatch06_indices = true ∧
     Batch.checkCRingBatch 11 Batch.cbatch07_indices = true ∧
     Batch.checkCRingBatch 11 Batch.cbatch08_indices = true ∧
     Batch.checkCRingBatch 11 Batch.cbatch09_indices = true ∧
     Batch.checkCRingBatch 11 Batch.cbatch10_indices = true ∧
     Batch.checkCRingBatch 11 Batch.cbatch11_indices = true) ∧
    (Batch.checkCRingBatch 12 Batch.cbatch12_indices = true ∧
     Batch.checkCRingBatch 12 Batch.cbatch13_indices = true ∧
     Batch.checkCRingBatch 12 Batch.cbatch14_indices = true ∧
     Batch.checkCRingBatch 12 Batch.cbatch15_indices = true ∧
     Batch.checkCRingBatch 12 Batch.cbatch16_indices = true ∧
     Batch.checkCRingBatch 12 Batch.cbatch17_indices = true ∧
     Batch.checkCRingBatch 12 Batch.cbatch18_indices = true ∧
     Batch.checkCRingBatch 12 Batch.cbatch19_indices = true ∧
     Batch.checkCRingBatch 12 Batch.cbatch20_indices = true ∧
     Batch.checkCRingBatch 12 Batch.cbatch21_indices = true ∧
     Batch.checkCRingBatch 12 Batch.cbatch22_indices = true ∧
     Batch.checkCRingBatch 12 Batch.cbatch23_indices = true ∧
     Batch.checkCRingBatch 12 Batch.cbatch24_indices = true ∧
     Batch.checkCRingBatch 12 Batch.cbatch25_indices = true) ∧
    (Batch.checkCRingBatch13 Batch.cbatch26_indices = true ∧
     Batch.checkCRingBatch13 Batch.cbatch27_indices = true ∧
     Batch.checkCRingBatch13 Batch.cbatch28_indices = true ∧
     Batch.checkCRingBatch13 Batch.cbatch29_indices = true ∧
     Batch.checkCRingBatch13 Batch.cbatch30_indices = true ∧
     Batch.checkCRingBatch13 Batch.cbatch31_indices = true ∧
     Batch.checkCRingBatch13 Batch.cbatch32_indices = true ∧
     Batch.checkCRingBatch13 Batch.cbatch33_indices = true ∧
     Batch.checkCRingBatch13 Batch.cbatch34_indices = true ∧
     Batch.checkCRingBatch13 Batch.cbatch35_indices = true ∧
     Batch.checkCRingBatch13 Batch.cbatch36_indices = true ∧
     Batch.checkCRingBatch13 Batch.cbatch37_indices = true ∧
     Batch.checkCRingBatch13 Batch.cbatch38_indices = true ∧
     Batch.checkCRingBatch13 Batch.cbatch39_indices = true ∧
     Batch.checkCRingBatch13 Batch.cbatch40_indices = true ∧
     Batch.checkCRingBatch13 Batch.cbatch41_indices = true ∧
     Batch.checkCRingBatch13 Batch.cbatch42_indices = true ∧
     Batch.checkCRingBatch13 Batch.cbatch43_indices = true ∧
     Batch.checkCRingBatch13 Batch.cbatch44_indices = true ∧
     Batch.checkCRingBatch13 Batch.cbatch45_indices = true ∧
     Batch.checkCRingBatch13 Batch.cbatch46_indices = true ∧
     Batch.checkCRingBatch13 Batch.cbatch47_indices = true ∧
     Batch.checkCRingBatch13 Batch.cbatch48_indices = true ∧
     Batch.checkCRingBatch13 Batch.cbatch49_indices = true) ∧
    (Batch.checkCRingBatch14 Batch.cbatch50_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch51_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch52_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch53_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch54_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch55_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch56_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch57_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch58_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch59_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch60_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch61_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch62_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch63_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch64_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch65_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch66_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch67_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch68_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch69_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch70_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch71_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch72_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch73_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch74_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch75_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch76_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch77_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch78_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch79_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch80_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch81_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch82_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch83_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch84_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch85_indices = true ∧
     Batch.checkCRingBatch14 Batch.cbatch86_indices = true)

/-- Master In-Kernel Certificate Suite Theorem:
    Explicitly witnesses that all in-kernel reflection batch theorems across ALL 10 ring suites
    (R6to10, R11, R12, R13, R14, CR8to10, CR11, CR12, CR13, CR14) — comprising all 138 batch
    reflection files covering all 633 configurations — are verified directly by Lean 4's kernel reduction. -/
theorem master_suite_verified : MasterSuiteVerifiedProp :=
  ⟨Batch.r6to10_batches_verified,
   Batch.r11_batches_verified,
   Batch.r12_batches_verified,
   Batch.r13_batches_verified,
   Batch.r14_batches_verified,
   Batch.cr8to10_batches_verified,
   Batch.cr11_batches_verified,
   Batch.cr12_batches_verified,
   Batch.cr13_batches_verified,
   Batch.cr14_batches_verified⟩

theorem all_append_d {l₁ l₂ : List Nat}
    (h₁ : l₁.all KernelReducer.verifyIdxD = true) (h₂ : l₂.all KernelReducer.verifyIdxD = true) :
    (l₁ ++ l₂).all KernelReducer.verifyIdxD = true := by
  rw [List.all_append, h₁, h₂]
  rfl

theorem all_append_c {l₁ l₂ : List Nat}
    (h₁ : l₁.all KernelReducer.verifyIdxC = true) (h₂ : l₂.all KernelReducer.verifyIdxC = true) :
    (l₁ ++ l₂).all KernelReducer.verifyIdxC = true := by
  rw [List.all_append, h₁, h₂]
  rfl

theorem to_all_d {r : Nat} {l : List Nat} (h : Batch.checkRingBatch r l = true) :
    l.all KernelReducer.verifyIdxD = true := by
  unfold Batch.checkRingBatch Batch.checkIdxFast at h
  exact h

theorem to_all_d13 {l : List Nat} (h : Batch.checkRingBatch13 l = true) :
    l.all KernelReducer.verifyIdxD = true := by
  unfold Batch.checkRingBatch13 Batch.checkIdxFast13 at h
  exact h

theorem to_all_d14 {l : List Nat} (h : Batch.checkRingBatch14 l = true) :
    l.all KernelReducer.verifyIdxD = true := by
  unfold Batch.checkRingBatch14 Batch.checkIdxFast14 at h
  exact h

theorem to_all_c {r : Nat} {l : List Nat} (h : Batch.checkCRingBatch r l = true) :
    l.all KernelReducer.verifyIdxC = true := by
  unfold Batch.checkCRingBatch Batch.checkIdxCFast at h
  exact h

theorem to_all_c13 {l : List Nat} (h : Batch.checkCRingBatch13 l = true) :
    l.all KernelReducer.verifyIdxC = true := by
  unfold Batch.checkCRingBatch13 Batch.checkIdxCFast13 at h
  exact h

theorem to_all_c14 {l : List Nat} (h : Batch.checkCRingBatch14 l = true) :
    l.all KernelReducer.verifyIdxC = true := by
  unfold Batch.checkCRingBatch14 Batch.checkIdxCFast14 at h
  exact h

/-- Every index in `certified_d_indices` passes the in-kernel D-reducibility verifier `KernelReducer.verifyIdxD`. -/
theorem certified_d_indices_all_verified :
    certified_d_indices.all KernelReducer.verifyIdxD = true := by
  rcases Batch.r6to10_batches_verified with ⟨hd1, hd2, hd3, hd4, hd5, hd6⟩
  rcases Batch.r11_batches_verified with ⟨hd7, hd8, hd9, hd10, hd11, hd12, hd13⟩
  rcases Batch.r12_batches_verified with ⟨hd14, hd15, hd16, hd17, hd18, hd19, hd20, hd21, hd22, hd23, hd24, hd25, hd26, hd27, hd28, hd29⟩
  rcases Batch.r13_batches_verified with ⟨hd30, hd31, hd32, hd33, hd34, hd35, hd36, hd37, hd38, hd39, hd40, hd41, hd42⟩
  rcases Batch.r14_batches_verified with ⟨hd43, hd44, hd45, hd46, hd47, hd48, hd49, hd50, hd51, hd52, hd53, hd54, hd55⟩
  have hr6to10 : Batch.certified_indices_r6to10.all KernelReducer.verifyIdxD = true := by
    unfold Batch.certified_indices_r6to10
    exact all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (to_all_d hd1) (to_all_d hd2)) (to_all_d hd3)) (to_all_d hd4)) (to_all_d hd5)) (to_all_d hd6)
  have hr11 : Batch.certified_indices_r11.all KernelReducer.verifyIdxD = true := by
    unfold Batch.certified_indices_r11
    exact all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (to_all_d hd7) (to_all_d hd8)) (to_all_d hd9)) (to_all_d hd10)) (to_all_d hd11)) (to_all_d hd12)) (to_all_d hd13)
  have hr12 : Batch.certified_indices_r12.all KernelReducer.verifyIdxD = true := by
    unfold Batch.certified_indices_r12
    exact all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (to_all_d hd14) (to_all_d hd15)) (to_all_d hd16)) (to_all_d hd17)) (to_all_d hd18)) (to_all_d hd19)) (to_all_d hd20)) (to_all_d hd21)) (to_all_d hd22)) (to_all_d hd23)) (to_all_d hd24)) (to_all_d hd25)) (to_all_d hd26)) (to_all_d hd27)) (to_all_d hd28)) (to_all_d hd29)
  have hr13 : Batch.certified_indices_r13.all KernelReducer.verifyIdxD = true := by
    unfold Batch.certified_indices_r13
    exact all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (to_all_d13 hd30) (to_all_d13 hd31)) (to_all_d13 hd32)) (to_all_d13 hd33)) (to_all_d13 hd34)) (to_all_d13 hd35)) (to_all_d13 hd36)) (to_all_d13 hd37)) (to_all_d13 hd38)) (to_all_d13 hd39)) (to_all_d13 hd40)) (to_all_d13 hd41)) (to_all_d13 hd42)
  have hr14 : Batch.certified_indices_r14.all KernelReducer.verifyIdxD = true := by
    unfold Batch.certified_indices_r14
    exact all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (all_append_d (to_all_d14 hd43) (to_all_d14 hd44)) (to_all_d14 hd45)) (to_all_d14 hd46)) (to_all_d14 hd47)) (to_all_d14 hd48)) (to_all_d14 hd49)) (to_all_d14 hd50)) (to_all_d14 hd51)) (to_all_d14 hd52)) (to_all_d14 hd53)) (to_all_d14 hd54)) (to_all_d14 hd55)
  unfold certified_d_indices
  exact all_append_d (all_append_d (all_append_d (all_append_d hr6to10 hr11) hr12) hr13) hr14

/-- Every index in `certified_c_indices` passes the in-kernel C-reducibility verifier `KernelReducer.verifyIdxC`. -/
theorem certified_c_indices_all_verified :
    certified_c_indices.all KernelReducer.verifyIdxC = true := by
  rcases Batch.cr8to10_batches_verified with ⟨hc1, hc2, hc3, hc4⟩
  rcases Batch.cr11_batches_verified with ⟨hc5, hc6, hc7, hc8, hc9, hc10, hc11⟩
  rcases Batch.cr12_batches_verified with ⟨hc12, hc13, hc14, hc15, hc16, hc17, hc18, hc19, hc20, hc21, hc22, hc23, hc24, hc25⟩
  rcases Batch.cr13_batches_verified with ⟨hc26, hc27, hc28, hc29, hc30, hc31, hc32, hc33, hc34, hc35, hc36, hc37, hc38, hc39, hc40, hc41, hc42, hc43, hc44, hc45, hc46, hc47, hc48, hc49⟩
  rcases Batch.cr14_batches_verified with ⟨hc50, hc51, hc52, hc53, hc54, hc55, hc56, hc57, hc58, hc59, hc60, hc61, hc62, hc63, hc64, hc65, hc66, hc67, hc68, hc69, hc70, hc71, hc72, hc73, hc74, hc75, hc76, hc77, hc78, hc79, hc80, hc81, hc82, hc83, hc84, hc85, hc86⟩
  have hcr8to10 : Batch.certified_indices_cr8to10.all KernelReducer.verifyIdxC = true := by
    unfold Batch.certified_indices_cr8to10
    exact all_append_c (all_append_c (all_append_c (to_all_c hc1) (to_all_c hc2)) (to_all_c hc3)) (to_all_c hc4)
  have hcr11 : Batch.certified_indices_cr11.all KernelReducer.verifyIdxC = true := by
    unfold Batch.certified_indices_cr11
    exact all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (to_all_c hc5) (to_all_c hc6)) (to_all_c hc7)) (to_all_c hc8)) (to_all_c hc9)) (to_all_c hc10)) (to_all_c hc11)
  have hcr12 : Batch.certified_indices_cr12.all KernelReducer.verifyIdxC = true := by
    unfold Batch.certified_indices_cr12
    exact all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (to_all_c hc12) (to_all_c hc13)) (to_all_c hc14)) (to_all_c hc15)) (to_all_c hc16)) (to_all_c hc17)) (to_all_c hc18)) (to_all_c hc19)) (to_all_c hc20)) (to_all_c hc21)) (to_all_c hc22)) (to_all_c hc23)) (to_all_c hc24)) (to_all_c hc25)
  have hcr13 : Batch.certified_indices_cr13.all KernelReducer.verifyIdxC = true := by
    unfold Batch.certified_indices_cr13
    exact all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (to_all_c13 hc26) (to_all_c13 hc27)) (to_all_c13 hc28)) (to_all_c13 hc29)) (to_all_c13 hc30)) (to_all_c13 hc31)) (to_all_c13 hc32)) (to_all_c13 hc33)) (to_all_c13 hc34)) (to_all_c13 hc35)) (to_all_c13 hc36)) (to_all_c13 hc37)) (to_all_c13 hc38)) (to_all_c13 hc39)) (to_all_c13 hc40)) (to_all_c13 hc41)) (to_all_c13 hc42)) (to_all_c13 hc43)) (to_all_c13 hc44)) (to_all_c13 hc45)) (to_all_c13 hc46)) (to_all_c13 hc47)) (to_all_c13 hc48)) (to_all_c13 hc49)
  have hcr14 : Batch.certified_indices_cr14.all KernelReducer.verifyIdxC = true := by
    unfold Batch.certified_indices_cr14
    exact all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (all_append_c (to_all_c14 hc50) (to_all_c14 hc51)) (to_all_c14 hc52)) (to_all_c14 hc53)) (to_all_c14 hc54)) (to_all_c14 hc55)) (to_all_c14 hc56)) (to_all_c14 hc57)) (to_all_c14 hc58)) (to_all_c14 hc59)) (to_all_c14 hc60)) (to_all_c14 hc61)) (to_all_c14 hc62)) (to_all_c14 hc63)) (to_all_c14 hc64)) (to_all_c14 hc65)) (to_all_c14 hc66)) (to_all_c14 hc67)) (to_all_c14 hc68)) (to_all_c14 hc69)) (to_all_c14 hc70)) (to_all_c14 hc71)) (to_all_c14 hc72)) (to_all_c14 hc73)) (to_all_c14 hc74)) (to_all_c14 hc75)) (to_all_c14 hc76)) (to_all_c14 hc77)) (to_all_c14 hc78)) (to_all_c14 hc79)) (to_all_c14 hc80)) (to_all_c14 hc81)) (to_all_c14 hc82)) (to_all_c14 hc83)) (to_all_c14 hc84)) (to_all_c14 hc85)) (to_all_c14 hc86)
  unfold certified_c_indices
  exact all_append_c (all_append_c (all_append_c (all_append_c hcr8to10 hcr11) hcr12) hcr13) hcr14

/-- Any index in `certified_d_indices` has `KernelReducer.verifyIdxD idx = true`. -/
theorem verifyIdxD_of_mem_certified_d (idx : Nat) (h : idx ∈ certified_d_indices) :
    KernelReducer.verifyIdxD idx = true :=
  List.all_eq_true.mp certified_d_indices_all_verified idx h

/-- Any index in `certified_c_indices` has `KernelReducer.verifyIdxC idx = true`. -/
theorem verifyIdxC_of_mem_certified_c (idx : Nat) (h : idx ∈ certified_c_indices) :
    KernelReducer.verifyIdxC idx = true :=
  List.all_eq_true.mp certified_c_indices_all_verified idx h

/-- Single-pass check over `parsedRConfList` that every configuration in `certified_c_indices`
    has a non-empty `contractEdges` list (short-circuiting in O(1) whenever `contractEdges` is non-empty). -/
def checkCConfigsHaveContracts : List FastReducer.RConf → Nat → Bool
  | [], _ => true
  | rc :: rest, idx =>
    (!(rc.contractEdges.toList.isEmpty) || !(certified_c_indices.contains idx)) &&
    checkCConfigsHaveContracts rest (idx + 1)

/-- In-kernel verification that all 384 C-certified configurations have non-empty `contractEdges`. -/
theorem c_configs_have_contracts_verified :
    checkCConfigsHaveContracts parsedRConfList 0 = true := by
  rfl

/-- In-kernel verification that every configuration index `0 .. 632` belongs either to
    `certified_d_indices` or to `certified_c_indices`. -/
theorem all_633_partitioned :
    (List.range 633).all (fun idx =>
      certified_d_indices.contains idx || certified_c_indices.contains idx) = true := by
  rfl

/-- Master In-Kernel Index Certification Theorem:
    For every canonical index `idx < 633`, the 138 in-kernel batch certificates
    unconditionally prove that either:
    1. `idx ∈ certified_d_indices` and `KernelReducer.verifyIdxD idx = true`, or
    2. `idx ∈ certified_c_indices` and `KernelReducer.verifyIdxC idx = true`. -/
theorem master_suite_certifies_idx (idx : Nat) (h_lt : idx < 633) :
    (idx ∈ certified_d_indices ∧ KernelReducer.verifyIdxD idx = true) ∨
    (idx ∈ certified_c_indices ∧ KernelReducer.verifyIdxC idx = true) := by
  have hMemRange : idx ∈ List.range 633 := List.mem_range.mpr h_lt
  have hPart := List.all_eq_true.mp all_633_partitioned idx hMemRange
  rw [Bool.or_eq_true] at hPart
  cases hPart with
  | inl hd_cont =>
    have hd_mem : idx ∈ certified_d_indices := List.mem_of_elem_eq_true hd_cont
    exact Or.inl ⟨hd_mem, verifyIdxD_of_mem_certified_d idx hd_mem⟩
  | inr hc_cont =>
    have hc_mem : idx ∈ certified_c_indices := List.mem_of_elem_eq_true hc_cont
    exact Or.inr ⟨hc_mem, verifyIdxC_of_mem_certified_c idx hc_mem⟩


/-- Soundness of `checkCConfigsHaveContracts`: any offset `k` where `base + k ∈ certified_c_indices`
    has a non-empty `contractEdges` list in `L[k]`. -/
theorem checkCConfigsHaveContracts_sound (L : List FastReducer.RConf) (base k : Nat)
    (h_chk : checkCConfigsHaveContracts L base = true)
    (hk : k < L.length)
    (hc : (base + k) ∈ certified_c_indices) :
    (L[k]'hk).contractEdges.toList ≠ [] := by
  induction L generalizing base k with
  | nil => contradiction
  | cons rc rest ih =>
    dsimp [checkCConfigsHaveContracts] at h_chk
    rw [Bool.and_eq_true] at h_chk
    cases k with
    | zero =>
      rw [Nat.add_zero] at hc
      have h_cont : certified_c_indices.contains base = true := List.elem_eq_true_of_mem hc
      have h_head := h_chk.1
      intro h_nil
      dsimp at h_nil
      rw [h_nil, h_cont] at h_head
      contradiction
    | succ k' =>
      have hk' : k' < rest.length := by
        dsimp at hk
        omega
      have hc' : (base + 1 + k') ∈ certified_c_indices := by
        have h_eq : base + 1 + k' = base + (k' + 1) := by omega
        rwa [h_eq]
      exact ih (base + 1) k' h_chk.2 hk' hc'

/-- Canonical precomputed signed matching table for configuration `c` at its ring size. -/
def canonicalSMData (c : Configuration) : Array SMData :=
  CheckerSoundness.buildSMDataTotal c.ringSize Batch.sharedPow3

/-- D-reducibility checker certificate package for configuration `c` at canonical index `idx`:
    `KernelReducer.verifyIdxD idx = true` (proved sound unconditionally via `KernelSoundness.verifyIdxD_sound`). -/
def HasDCertificateWitness (_c : Configuration) (idx : Nat) : Prop :=
  KernelReducer.verifyIdxD idx = true

/-- C-reducibility checker certificate package for configuration `c` at canonical index `idx`:
    `KernelReducer.verifyIdxC idx = true` (proved sound unconditionally via `KernelSoundness.verifyIdxC_sound`). -/
def HasCCertificateWitness (_c : Configuration) (idx : Nat) : Prop :=
  KernelReducer.verifyIdxC idx = true

/-- Kernel-to-Mathematical Certificate Soundness Bridge:
    Connects `KernelReducer.verifyIdxD idx = true` to `HasDCertificateWitness` and
    `idx ∈ certified_c_indices → KernelReducer.verifyIdxC idx = true` to `HasCCertificateWitness`. -/
def KernelReducerSoundnessBridge : Prop :=
  ∀ (idx : Nat) (h_lt : idx < 633),
    let c := theUnavoidableSet[idx]'(by rw [unavoidable_size_eq]; exact h_lt)
    (KernelReducer.verifyIdxD idx = true → HasDCertificateWitness c idx) ∧
    (idx ∈ certified_c_indices → KernelReducer.verifyIdxC idx = true → HasCCertificateWitness c idx)

/-- Unconditional proof of `KernelReducerSoundnessBridge`. -/
theorem kernel_reducer_soundness_bridge : KernelReducerSoundnessBridge :=
  fun _ _ => ⟨fun h => h, fun _ h => h⟩

/-- Batch certificate soundness bridge across all 633 canonical configurations. -/
def HasBatchSoundnessBridge : Prop :=
  ∀ (idx : Nat) (h_lt : idx < 633),
    let c := theUnavoidableSet[idx]'(by rw [unavoidable_size_eq]; exact h_lt)
    (idx ∈ certified_d_indices ∧ HasDCertificateWitness c idx) ∨
    (idx ∈ certified_c_indices ∧ HasCCertificateWitness c idx)

/-- Derivation of `HasBatchSoundnessBridge` from `KernelReducerSoundnessBridge` and `master_suite_certifies_idx`:
    Every index `idx < 633` is dispatched by the 138 in-kernel batch certificates to either
    `certified_d_indices` (with `verifyIdxD idx = true`) or `certified_c_indices` (with `verifyIdxC idx = true`). -/
theorem batch_soundness_of_kernel_bridge (hK : KernelReducerSoundnessBridge) :
    HasBatchSoundnessBridge := by
  intro idx h_lt
  have hCert := master_suite_certifies_idx idx h_lt
  have hKB := hK idx h_lt
  cases hCert with
  | inl hd =>
    exact Or.inl ⟨hd.1, hKB.1 hd.2⟩
  | inr hc =>
    exact Or.inr ⟨hc.1, hKB.2 hc.1 hc.2⟩

/-- Unconditional proof of `HasBatchSoundnessBridge` across all 633 canonical configurations. -/
theorem rsst_batch_soundness_bridge : HasBatchSoundnessBridge :=
  batch_soundness_of_kernel_bridge kernel_reducer_soundness_bridge

/-- An unavoidable configuration is certified in the in-kernel RSST batch test suite
    if the master suite of all 138 batch reflection theorems holds, and its canonical
    index in the RSST dataset is certified by either a D-reduction or C-reduction batch theorem. -/
def isCertifiedUnavoidableConfig (c : Configuration) : Prop :=
  MasterSuiteVerifiedProp ∧
  ∃ (idx : Nat) (h_lt : idx < 633),
    theUnavoidableSet[idx]'(by rw [unavoidable_size_eq]; exact h_lt) = c ∧
    ((idx ∈ certified_d_indices ∧ HasDCertificateWitness c idx) ∨
     (idx ∈ certified_c_indices ∧ HasCCertificateWitness c idx))

/-- A configuration is certified D-reducible in the RSST batch suite if its canonical
    index belongs to certified_d_indices and the master batch suite is verified. -/
def isCertifiedDConfig (c : Configuration) : Prop :=
  MasterSuiteVerifiedProp ∧
  ∃ (idx : Nat) (h_lt : idx < 633),
    theUnavoidableSet[idx]'(by rw [unavoidable_size_eq]; exact h_lt) = c ∧
    idx ∈ certified_d_indices ∧
    HasDCertificateWitness c idx

/-- A configuration is certified C-reducible in the RSST batch suite if its canonical
    index belongs to certified_c_indices and the master batch suite is verified. -/
def isCertifiedCConfig (c : Configuration) : Prop :=
  MasterSuiteVerifiedProp ∧
  ∃ (idx : Nat) (h_lt : idx < 633),
    theUnavoidableSet[idx]'(by rw [unavoidable_size_eq]; exact h_lt) = c ∧
    idx ∈ certified_c_indices ∧
    HasCCertificateWitness c idx

/-- Certified unavoidable configurations partition into D-certified and C-certified configurations. -/
theorem certified_cases_iff (c : Configuration) :
    isCertifiedUnavoidableConfig c ↔ isCertifiedDConfig c ∨ isCertifiedCConfig c := by
  constructor
  · rintro ⟨hMaster, idx, h_lt, h_eq, h_cases⟩
    cases h_cases with
    | inl hd => exact Or.inl ⟨hMaster, idx, h_lt, h_eq, hd.1, hd.2⟩
    | inr hc => exact Or.inr ⟨hMaster, idx, h_lt, h_eq, hc.1, hc.2⟩
  · rintro (⟨hMaster, idx, h_lt, h_eq, hd, hdw⟩ | ⟨hMaster, idx, h_lt, h_eq, hc, hcw⟩)
    · exact ⟨hMaster, idx, h_lt, h_eq, Or.inl ⟨hd, hdw⟩⟩
    · exact ⟨hMaster, idx, h_lt, h_eq, Or.inr ⟨hc, hcw⟩⟩

/-- Master In-Kernel Certificate Theorem:
    Every configuration in the canonical RSST unavoidable set is certified reducible
    by the in-kernel batch suite (either D-reducible or C-reducible), witnessed directly
    by the master suite proof of all 138 computational batch theorems. -/
theorem all_unavoidable_configs_certified (c : Configuration)
    (h : c ∈ theUnavoidableSet) :
    isCertifiedUnavoidableConfig c := by
  rcases Array.getElem_of_mem h with ⟨idx, h_idx_lt, h_get⟩
  have h_size : theUnavoidableSet.size = 633 := unavoidable_size_eq
  have h_lt : idx < 633 := by
    rw [← h_size]
    exact h_idx_lt
  have h_eq : theUnavoidableSet[idx]'(by rw [unavoidable_size_eq]; exact h_lt) = c := h_get
  have hB := rsst_batch_soundness_bridge idx h_lt
  refine ⟨master_suite_verified, idx, h_lt, h_eq, ?_⟩
  rw [← h_eq]
  exact hB

/-- General connection between `Array.getElem` and `getElem!`. -/
theorem array_get_eq_getElem! {α : Type} [Inhabited α] (arr : Array α) (idx : Nat) (h_sz : idx < arr.size) :
    arr[idx]'h_sz = arr[idx]! := by
  rw [getElem!_pos arr idx h_sz]

/-- Connection between indexed get on theUnavoidableSet and getElem!. -/
theorem unavoidable_get_eq_getElem! (idx : Nat) (h_lt : idx < 633) :
    theUnavoidableSet[idx]'(by rw [unavoidable_size_eq]; exact h_lt) = theUnavoidableSet[idx]! :=
  array_get_eq_getElem! theUnavoidableSet idx (by rw [unavoidable_size_eq]; exact h_lt)

/-- Every C-certified configuration index `idx < 633` has a non-empty `contractEdges` list,
    proved unconditionally from `c_configs_have_contracts_verified`. -/
theorem c_contract_edges_nonempty (idx : Nat) (h_lt : idx < 633) (hc : idx ∈ certified_c_indices) :
    (theUnavoidableSet[idx]'(by rw [unavoidable_size_eq]; exact h_lt)).contractEdges ≠ [] := by
  rw [unavoidable_get_eq_getElem! idx h_lt, theUnavoidableSet_getElem! idx h_lt]
  dsimp [configOfRConf]
  have h_len : idx < parsedRConfList.length := by
    rw [parsedRConfList_length]; exact h_lt
  have h_arr : Batch.sharedCfgs[idx]! = parsedRConfList[idx]'h_len := by
    let arr : Array FastReducer.RConf := ⟨parsedRConfList⟩
    have h_sz : idx < arr.size := h_len
    change arr[idx]! = parsedRConfList[idx]'h_len
    rw [getElem!_pos arr idx h_sz]
    rfl
  rw [h_arr]
  have hc0 : (0 + idx) ∈ certified_c_indices := by rw [Nat.zero_add]; exact hc
  exact checkCConfigsHaveContracts_sound parsedRConfList 0 idx c_configs_have_contracts_verified h_len hc0

/-- **Stage A + D4 D-Reducibility Soundness Theorem (`rsst_d_sound_of_checkFast`):**
    For any unavoidable configuration `c = theUnavoidableSet[idx]!` (`idx < 633`),
    `IsRingCycle`, `IsSoundEarlier`, `IsWellFormedEarlier`, `IsIrreflexiveAdj`, `c.ringSize ≤ 15`,
    `FullRepresentationHypothesis`, `InitialLiveSpec`, and `IterationEliminationHypothesis` are all
    discharged unconditionally, reducing `IsDReducible c` solely to `checkFastTotal = true`. -/
theorem rsst_d_sound_of_checkFast (c : Configuration) (idx : Nat) (h_lt : idx < 633)
    (h_c_eq : c = theUnavoidableSet[idx]!)
    (h_check : Soundness.checkFastTotal (Soundness.rconfOfConfig c sharedCfgs[idx]!.earlier)
      (canonicalSMData c) Batch.sharedPow3 = true) :
    IsDReducible c := by
  have h_ring : CheckerSoundness.IsRingCycle c := by
    rw [h_c_eq]
    exact CheckerSoundness.unavoidable_is_ring_cycle idx h_lt
  have h_irrefl : Soundness.IsIrreflexiveAdj c := by
    rw [h_c_eq]
    exact Soundness.unavoidable_is_irreflexive idx h_lt
  have h_earlier : Soundness.IsSoundEarlier c sharedCfgs[idx]!.earlier := by
    rw [h_c_eq]
    exact Soundness.unavoidable_is_sound_earlier idx h_lt
  have h_wf : Soundness.IsWellFormedEarlier c sharedCfgs[idx]!.earlier := by
    rw [h_c_eq]
    exact CheckerSoundness.unavoidable_is_well_formed_earlier idx h_lt
  have hr_le : c.ringSize ≤ 15 := by
    rw [h_c_eq]
    exact CheckerSoundness.unavoidable_ring_le_15 idx h_lt
  exact CheckerSoundness.fast_d_sound_canonical_of_wellFormed c sharedCfgs[idx]!.earlier
    h_check h_ring h_earlier h_wf h_irrefl hr_le

/-- **Stage A + D4 + C2 C-Reducibility Soundness Theorem (`rsst_c_sound_of_contract_check`):**
    For any C-certified unavoidable configuration `c = theUnavoidableSet[idx]!` (`idx < 633`, `idx ∈ certified_c_indices`),
    `c.contractEdges ≠ []`, `IsRingCycle`, `IsSoundEarlier`, `IsWellFormedEarlier`, `IsIrreflexiveAdj`,
    `c.ringSize ≤ 15`, `FullRepresentationHypothesis`, `InitialLiveSpec`,
    `LiveZeroIterationEliminationHypothesis`, and `ContractCheckSoundnessHypothesis` are all
    discharged unconditionally, reducing `IsCReducible c` solely to `runContractCheckTotal = true`. -/
theorem rsst_c_sound_of_contract_check (c : Configuration) (idx : Nat) (h_lt : idx < 633)
    (hc : idx ∈ certified_c_indices)
    (h_c_eq : c = theUnavoidableSet[idx]!)
    (h_run : Soundness.runContractCheckTotal (Soundness.rconfOfConfig c sharedCfgs[idx]!.earlier) Batch.sharedPow3
      (Soundness.computeFinalState (Soundness.rconfOfConfig c sharedCfgs[idx]!.earlier) (canonicalSMData c) Batch.sharedPow3).live = true) :
    IsCReducible c := by
  have h_contract : c.contractEdges ≠ [] := by
    rw [h_c_eq, ← unavoidable_get_eq_getElem! idx h_lt]
    exact c_contract_edges_nonempty idx h_lt hc
  have h_ring : CheckerSoundness.IsRingCycle c := by
    rw [h_c_eq]
    exact CheckerSoundness.unavoidable_is_ring_cycle idx h_lt
  have h_irrefl : Soundness.IsIrreflexiveAdj c := by
    rw [h_c_eq]
    exact Soundness.unavoidable_is_irreflexive idx h_lt
  have h_earlier : Soundness.IsSoundEarlier c sharedCfgs[idx]!.earlier := by
    rw [h_c_eq]
    exact Soundness.unavoidable_is_sound_earlier idx h_lt
  have h_wf : Soundness.IsWellFormedEarlier c sharedCfgs[idx]!.earlier := by
    rw [h_c_eq]
    exact CheckerSoundness.unavoidable_is_well_formed_earlier idx h_lt
  have hr_le : c.ringSize ≤ 15 := by
    rw [h_c_eq]
    exact CheckerSoundness.unavoidable_ring_le_15 idx h_lt
  exact CheckerSoundness.fast_c_sound_canonical_of_wellFormed c sharedCfgs[idx]!.earlier
    h_contract h_ring h_earlier h_wf h_irrefl hr_le h_run

/-- RSST D-Certificate Witness Theorem:
    Unpacks `isCertifiedDConfig c` into `verifyIdxD idx = true`. -/
theorem rsst_d_certificate_witness (c : Configuration) :
  isCertifiedDConfig c →
    ∃ (idx : Nat) (h_lt : idx < 633),
      theUnavoidableSet[idx]'(by rw [unavoidable_size_eq]; exact h_lt) = c ∧
      KernelReducer.verifyIdxD idx = true := by
  rintro ⟨_hMaster, idx, h_lt, h_eq, _hd, h_ver⟩
  exact ⟨idx, h_lt, h_eq, h_ver⟩

/-- RSST D-Certificate Soundness Theorem:
    A configuration certified as D-reducible is mathematically D-reducible,
    proved unconditionally via `KernelSoundness.verifyIdxD_sound`. -/
theorem rsst_d_certificate_soundness (c : Configuration) (h : isCertifiedDConfig c) :
    IsDReducible c := by
  rcases rsst_d_certificate_witness c h with ⟨idx, h_lt, h_eq, h_ver⟩
  have h_c_eq : c = theUnavoidableSet[idx]! := by
    rw [← h_eq, unavoidable_get_eq_getElem! idx h_lt]
  rw [h_c_eq]
  exact KernelSoundness.verifyIdxD_sound idx h_lt h_ver

/-- RSST C-Certificate Witness Theorem:
    Unpacks `isCertifiedCConfig c` into `idx ∈ certified_c_indices` and `verifyIdxC idx = true`. -/
theorem rsst_c_certificate_witness (c : Configuration) :
  isCertifiedCConfig c →
    ∃ (idx : Nat) (h_lt : idx < 633),
      theUnavoidableSet[idx]'(by rw [unavoidable_size_eq]; exact h_lt) = c ∧
      idx ∈ certified_c_indices ∧
      KernelReducer.verifyIdxC idx = true := by
  rintro ⟨_hMaster, idx, h_lt, h_eq, hc, h_ver⟩
  exact ⟨idx, h_lt, h_eq, hc, h_ver⟩

/-- RSST C-Certificate Soundness Theorem:
    A configuration certified as C-reducible is mathematically C-reducible,
    proved unconditionally via `KernelSoundness.verifyIdxC_sound`. -/
theorem rsst_c_certificate_soundness (c : Configuration) (h : isCertifiedCConfig c) :
    IsCReducible c := by
  rcases rsst_c_certificate_witness c h with ⟨idx, h_lt, h_eq, hc, h_ver⟩
  have h_c_eq : c = theUnavoidableSet[idx]! := by
    rw [← h_eq, unavoidable_get_eq_getElem! idx h_lt]
  have h_contract : (theUnavoidableSet[idx]!).contractEdges ≠ [] := by
    rw [← unavoidable_get_eq_getElem! idx h_lt]
    exact c_contract_edges_nonempty idx h_lt hc
  rw [h_c_eq]
  exact KernelSoundness.verifyIdxC_sound idx h_lt h_contract h_ver

/-- The RSST Certificate Soundness Principle:
    A configuration certified by the RSST in-kernel reflection suite across all 138 batch files
    is mathematically reducible (D-reducible if D-certified, or C-reducible if C-certified). -/
theorem rsst_certificate_soundness (c : Configuration) :
    isCertifiedUnavoidableConfig c → IsReducible c := by
  intro h
  rw [certified_cases_iff] at h
  cases h with
  | inl hD => exact Or.inl (rsst_d_certificate_soundness c hD)
  | inr hC => exact Or.inr (rsst_c_certificate_soundness c hC)

/-- **Unconditional Computational Reducibility of the RSST Unavoidable Set:**
    Every configuration in the canonical 633 unavoidable set is mathematically reducible,
    proved unconditionally from the 138 in-kernel batch certificates and `KernelSoundness`. -/
theorem rsst_all_unavoidable_reducible (c : Configuration)
    (hMem : c ∈ theUnavoidableSet) :
    IsReducible c := by
  have hCert := all_unavoidable_configs_certified c hMem
  rw [certified_cases_iff] at hCert
  cases hCert with
  | inl hD => exact Or.inl (rsst_d_certificate_soundness c hD)
  | inr hC => exact Or.inr (rsst_c_certificate_soundness c hC)

end MasterCertificate
end Math
