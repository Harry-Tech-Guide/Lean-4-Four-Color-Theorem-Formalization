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

/-- Index list of the 52 certified D-reducible configurations for ring size 13. -/
def certified_indices_r13 : List Nat :=
  [ 86, 87, 90, 105,
    106, 107, 167, 170,
    190, 207, 208, 210,
    219, 271, 272, 273,
    275, 383, 385, 394,
    395, 399, 438, 471,
    472, 482, 491, 511,
    513, 514, 517, 524,
    525, 526, 528, 529,
    536, 564, 565, 589,
    593, 594, 604, 606,
    607, 608, 611, 615,
    627, 628, 630, 631 ]

theorem certified_count_r13_eq : certified_indices_r13.length = certified_count_r13 := by
  rfl

end Batch
end Math
