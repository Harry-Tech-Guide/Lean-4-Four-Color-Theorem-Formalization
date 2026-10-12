import FourColorTheorem.Math.FastReducer

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 1: Rings 6 through 9

This module certifies the D-reducibility of all 13 D-reducible configurations
from the RSST unavoidable set with ring size ≤ 9.

Every theorem is verified directly inside the Lean 4 kernel via `native_decide`,
depending only on Lean's kernel reflection axiom `Lean.ofReduceBool`.

Summary of configurations certified in this module:
- Ring 6 (1 configuration): Config 0 (Birkhoff Diamond)
- Ring 7 (1 configuration): Config 1
- Ring 8 (4 configurations): Configs 2, 4, 7, 23
- Ring 9 (7 configurations): Configs 5, 6, 11, 24, 26, 37, 323
Total: 13 D-reducible configurations.
-/

private def pow3 := powers3 15
private def md6 := buildMData 6 pow3
private def md7 := buildMData 7 pow3
private def md8 := buildMData 8 pow3
private def md9 := buildMData 9 pow3

private def cfgs := loadAll ()

-- ============================================================================
-- Ring 6 (1 configuration)
-- ============================================================================

/-- Config 0 (RSST ID 0.7322, ring 6, Birkhoff Diamond): D-reducible. -/
theorem cert_config_0_d_red : (check cfgs[0]! md6 pow3).dReducible = true := by
  native_decide

-- ============================================================================
-- Ring 7 (1 configuration)
-- ============================================================================

/-- Config 1 (RSST ID 2.122, ring 7): D-reducible. -/
theorem cert_config_1_d_red : (check cfgs[1]! md7 pow3).dReducible = true := by
  native_decide

-- ============================================================================
-- Ring 8 (4 configurations)
-- ============================================================================

/-- Config 2 (RSST ID 3.442802, ring 8): D-reducible. -/
theorem cert_config_2_d_red : (check cfgs[2]! md8 pow3).dReducible = true := by
  native_decide

/-- Config 4 (RSST ID 0.453962, ring 8): D-reducible. -/
theorem cert_config_4_d_red : (check cfgs[4]! md8 pow3).dReducible = true := by
  native_decide

/-- Config 7 (RSST ID 0.4578, ring 8): D-reducible. -/
theorem cert_config_7_d_red : (check cfgs[7]! md8 pow3).dReducible = true := by
  native_decide

/-- Config 23 (RSST ID 0.1772, ring 8): D-reducible. -/
theorem cert_config_23_d_red : (check cfgs[23]! md8 pow3).dReducible = true := by
  native_decide

-- ============================================================================
-- Ring 9 (7 configurations)
-- ============================================================================

/-- Config 5 (RSST ID 3.1306802, ring 9): D-reducible. -/
theorem cert_config_5_d_red : (check cfgs[5]! md9 pow3).dReducible = true := by
  native_decide

/-- Config 6 (RSST ID 2.7566, ring 9): D-reducible. -/
theorem cert_config_6_d_red : (check cfgs[6]! md9 pow3).dReducible = true := by
  native_decide

/-- Config 11 (RSST ID 0.8142, ring 9): D-reducible. -/
theorem cert_config_11_d_red : (check cfgs[11]! md9 pow3).dReducible = true := by
  native_decide

/-- Config 24 (RSST ID 0.2016, ring 9): D-reducible. -/
theorem cert_config_24_d_red : (check cfgs[24]! md9 pow3).dReducible = true := by
  native_decide

/-- Config 26 (RSST ID 0.1804, ring 9): D-reducible. -/
theorem cert_config_26_d_red : (check cfgs[26]! md9 pow3).dReducible = true := by
  native_decide

/-- Config 37 (RSST ID 0.8144, ring 9): D-reducible. -/
theorem cert_config_37_d_red : (check cfgs[37]! md9 pow3).dReducible = true := by
  native_decide

/-- Config 323 (RSST ID 2.7582, ring 9): D-reducible. -/
theorem cert_config_323_d_red : (check cfgs[323]! md9 pow3).dReducible = true := by
  native_decide

end Batch
end Math
