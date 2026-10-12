import FourColorTheorem.Math.FastReducer

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 4: Ring 11 (Part 1)

This module certifies the D-reducibility of the first 11 D-reducible configurations
from the RSST unavoidable set with ring size 11:
Configs 15, 16, 17, 20, 40, 43, 49, 50, 52, 56, 58.

Every theorem is verified directly inside the Lean 4 kernel via `native_decide`,
depending solely on Lean's kernel reflection axiom `Lean.ofReduceBool`.
-/

private def pow3 := powers3 15
private def md11 := buildMData 11 pow3
private def cfgs := loadAll ()

/-- Config 15 (ring 11): D-reducible. -/
theorem cert_config_15_d_red : (check cfgs[15]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 16 (ring 11): D-reducible. -/
theorem cert_config_16_d_red : (check cfgs[16]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 17 (ring 11): D-reducible. -/
theorem cert_config_17_d_red : (check cfgs[17]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 20 (ring 11): D-reducible. -/
theorem cert_config_20_d_red : (check cfgs[20]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 40 (ring 11): D-reducible. -/
theorem cert_config_40_d_red : (check cfgs[40]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 43 (ring 11): D-reducible. -/
theorem cert_config_43_d_red : (check cfgs[43]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 49 (ring 11): D-reducible. -/
theorem cert_config_49_d_red : (check cfgs[49]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 50 (ring 11): D-reducible. -/
theorem cert_config_50_d_red : (check cfgs[50]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 52 (ring 11): D-reducible. -/
theorem cert_config_52_d_red : (check cfgs[52]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 56 (ring 11): D-reducible. -/
theorem cert_config_56_d_red : (check cfgs[56]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 58 (ring 11): D-reducible. -/
theorem cert_config_58_d_red : (check cfgs[58]! md11 pow3).dReducible = true := by
  native_decide

end Batch
end Math
