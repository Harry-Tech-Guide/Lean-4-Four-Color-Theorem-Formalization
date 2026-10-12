import FourColorTheorem.Math.FastReducer

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 2: Ring 10 (Part 1)

This module certifies the D-reducibility of the first 11 D-reducible configurations
from the RSST unavoidable set with ring size 10:
Configs 8, 9, 12, 13, 18, 27, 29, 30, 32, 36, 44.

Every theorem is verified directly inside the Lean 4 kernel via `native_decide`,
depending solely on Lean's kernel reflection axiom `Lean.ofReduceBool`.
-/

private def pow3 := powers3 15
private def md10 := buildMData 10 pow3
private def cfgs := loadAll ()

/-- Config 8 (ring 10): D-reducible. -/
theorem cert_config_8_d_red : (check cfgs[8]! md10 pow3).dReducible = true := by
  native_decide

/-- Config 9 (ring 10): D-reducible. -/
theorem cert_config_9_d_red : (check cfgs[9]! md10 pow3).dReducible = true := by
  native_decide

/-- Config 12 (ring 10): D-reducible. -/
theorem cert_config_12_d_red : (check cfgs[12]! md10 pow3).dReducible = true := by
  native_decide

/-- Config 13 (ring 10): D-reducible. -/
theorem cert_config_13_d_red : (check cfgs[13]! md10 pow3).dReducible = true := by
  native_decide

/-- Config 18 (ring 10): D-reducible. -/
theorem cert_config_18_d_red : (check cfgs[18]! md10 pow3).dReducible = true := by
  native_decide

/-- Config 27 (ring 10): D-reducible. -/
theorem cert_config_27_d_red : (check cfgs[27]! md10 pow3).dReducible = true := by
  native_decide

/-- Config 29 (ring 10): D-reducible. -/
theorem cert_config_29_d_red : (check cfgs[29]! md10 pow3).dReducible = true := by
  native_decide

/-- Config 30 (ring 10): D-reducible. -/
theorem cert_config_30_d_red : (check cfgs[30]! md10 pow3).dReducible = true := by
  native_decide

/-- Config 32 (ring 10): D-reducible. -/
theorem cert_config_32_d_red : (check cfgs[32]! md10 pow3).dReducible = true := by
  native_decide

/-- Config 36 (ring 10): D-reducible. -/
theorem cert_config_36_d_red : (check cfgs[36]! md10 pow3).dReducible = true := by
  native_decide

/-- Config 44 (ring 10): D-reducible. -/
theorem cert_config_44_d_red : (check cfgs[44]! md10 pow3).dReducible = true := by
  native_decide

end Batch
end Math
