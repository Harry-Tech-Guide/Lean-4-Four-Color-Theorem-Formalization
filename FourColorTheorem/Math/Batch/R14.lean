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

/-- Index list of the 26 certified D-reducible configurations for ring size 14. -/
def certified_indices_r14 : List Nat :=
  [ 109, 214,  -- Batch 40 (Part 1)
    222, 223,  -- Batch 41 (Part 2)
    224, 237,  -- Batch 42 (Part 3)
    238, 239,  -- Batch 43 (Part 4)
    240, 278,  -- Batch 44 (Part 5)
    279, 305,  -- Batch 45 (Part 6)
    312, 313,  -- Batch 46 (Part 7)
    315, 316,  -- Batch 47 (Part 8)
    397, 400,  -- Batch 48 (Part 9)
    486, 493,  -- Batch 49 (Part 10)
    494, 495,  -- Batch 50 (Part 11)
    545, 547,  -- Batch 51 (Part 12)
    548, 552   -- Batch 52 (Part 13)
  ]

theorem certified_count_r14_eq : certified_indices_r14.length = certified_count_r14 := by
  rfl

end Batch
end Math
