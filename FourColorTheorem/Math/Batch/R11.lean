module

public import FourColorTheorem.Math.Batch.Runner
public import FourColorTheorem.Math.Batch.Batch04_R11_Part1
public import FourColorTheorem.Math.Batch.Batch05_R11_Part2
public import FourColorTheorem.Math.Batch.Batch06_R11_Part3
public import FourColorTheorem.Math.Batch.Batch07_R11_Part4
public import FourColorTheorem.Math.Batch.Batch08_R11_Part5
public import FourColorTheorem.Math.Batch.Batch09_R11_Part6
public import FourColorTheorem.Math.Batch.Batch10_R11_Part7

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math
namespace Batch

open FastReducer

def batch04_indices : List Nat := [15, 16, 17, 20, 40, 43, 49, 50, 52, 56, 58]
def batch05_indices : List Nat := [60, 69, 70, 71, 77, 81]
def batch06_indices : List Nat := [104, 114, 117, 119, 120, 129]
def batch07_indices : List Nat := [133, 201, 330, 332, 334, 336]
def batch08_indices : List Nat := [337, 348, 349, 354, 362]
def batch09_indices : List Nat := [401, 404, 423, 424, 567]
def batch10_indices : List Nat := [568, 570, 571, 582, 621]
def certified_count_r11 : Nat := 44
def certified_indices_r11 : List Nat :=
  batch04_indices ++ batch05_indices ++ batch06_indices ++ batch07_indices ++ batch08_indices ++ batch09_indices ++ batch10_indices
theorem certified_count_r11_eq : certified_indices_r11.length = certified_count_r11 := by rfl

theorem cert_batch04_r11 : checkRingBatch 11 batch04_indices = true := by
  dsimp only [batch04_indices, checkRingBatch, List.all]; rw [cert_config_15_d_red, cert_config_16_d_red, cert_config_17_d_red, cert_config_20_d_red, cert_config_40_d_red, cert_config_43_d_red, cert_config_49_d_red, cert_config_50_d_red, cert_config_52_d_red, cert_config_56_d_red, cert_config_58_d_red]; rfl
theorem cert_batch05_r11 : checkRingBatch 11 batch05_indices = true := by
  dsimp only [batch05_indices, checkRingBatch, List.all]; rw [cert_config_60_d_red, cert_config_69_d_red, cert_config_70_d_red, cert_config_71_d_red, cert_config_77_d_red, cert_config_81_d_red]; rfl
theorem cert_batch06_r11 : checkRingBatch 11 batch06_indices = true := by
  dsimp only [batch06_indices, checkRingBatch, List.all]; rw [cert_config_104_d_red, cert_config_114_d_red, cert_config_117_d_red, cert_config_119_d_red, cert_config_120_d_red, cert_config_129_d_red]; rfl
theorem cert_batch07_r11 : checkRingBatch 11 batch07_indices = true := by
  dsimp only [batch07_indices, checkRingBatch, List.all]; rw [cert_config_133_d_red, cert_config_201_d_red, cert_config_330_d_red, cert_config_332_d_red, cert_config_334_d_red, cert_config_336_d_red]; rfl
theorem cert_batch08_r11 : checkRingBatch 11 batch08_indices = true := by
  dsimp only [batch08_indices, checkRingBatch, List.all]; rw [cert_config_337_d_red, cert_config_348_d_red, cert_config_349_d_red, cert_config_354_d_red, cert_config_362_d_red]; rfl
theorem cert_batch09_r11 : checkRingBatch 11 batch09_indices = true := by
  dsimp only [batch09_indices, checkRingBatch, List.all]; rw [cert_config_401_d_red, cert_config_404_d_red, cert_config_423_d_red, cert_config_424_d_red, cert_config_567_d_red]; rfl
theorem cert_batch10_r11 : checkRingBatch 11 batch10_indices = true := by
  dsimp only [batch10_indices, checkRingBatch, List.all]; rw [cert_config_568_d_red, cert_config_570_d_red, cert_config_571_d_red, cert_config_582_d_red, cert_config_621_d_red]; rfl

theorem r11_batches_verified :
    checkRingBatch 11 batch04_indices = true ∧
    checkRingBatch 11 batch05_indices = true ∧
    checkRingBatch 11 batch06_indices = true ∧
    checkRingBatch 11 batch07_indices = true ∧
    checkRingBatch 11 batch08_indices = true ∧
    checkRingBatch 11 batch09_indices = true ∧
    checkRingBatch 11 batch10_indices = true :=
  ⟨cert_batch04_r11, cert_batch05_r11, cert_batch06_r11, cert_batch07_r11, cert_batch08_r11, cert_batch09_r11, cert_batch10_r11⟩
end Batch
end Math
