import FourColorTheorem.Math.Batch.CRunner14

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel C-Reducibility Batch 53: Ring 14 (Part 4)

This module certifies the C-reducibility of 3 C-reducible configurations
from the RSST unavoidable set with ring size 14:
Configs 226, 227, 228.
-/

/-- The 3 ring-14 configuration indices certified in CBatch 53. -/
def cbatch53_indices : List Nat :=
  [226, 227, 228]

/-- Unified in-kernel certification for CBatch 53 (Ring 14, Part 4). -/
theorem cert_cbatch53_r14 : checkCRingBatch14 cbatch53_indices = true := by
  native_decide

-- Individual configuration certificates extracted deductively from the batch theorem:

theorem cert_config_226_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 226 = true :=
  certified_of_cbatch14 cbatch53_indices cert_cbatch53_r14 226 (by decide)

theorem cert_config_227_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 227 = true :=
  certified_of_cbatch14 cbatch53_indices cert_cbatch53_r14 227 (by decide)

theorem cert_config_228_c_red : checkIdxCFast14 (buildSMData 14 sharedPow3) 228 = true :=
  certified_of_cbatch14 cbatch53_indices cert_cbatch53_r14 228 (by decide)

end Batch
end Math
