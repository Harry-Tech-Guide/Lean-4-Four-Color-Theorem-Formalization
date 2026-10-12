import FourColorTheorem.Math.FastReducer

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 8: Ring 11 (Part 5)

This module certifies the D-reducibility of 5 configurations
from the RSST unavoidable set with ring size 11:
Configs 337, 348, 349, 354, 362.

Every theorem is verified directly inside the Lean 4 kernel via `native_decide`,
depending solely on Lean's kernel reflection axiom `Lean.ofReduceBool`.
-/

private def pow3 := powers3 15
private def md11 := buildMData 11 pow3
private def cfgs := loadAll ()

/-- Config 337 (ring 11): D-reducible. -/
theorem cert_config_337_d_red : (check cfgs[337]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 348 (ring 11): D-reducible. -/
theorem cert_config_348_d_red : (check cfgs[348]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 349 (ring 11): D-reducible. -/
theorem cert_config_349_d_red : (check cfgs[349]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 354 (ring 11): D-reducible. -/
theorem cert_config_354_d_red : (check cfgs[354]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 362 (ring 11): D-reducible. -/
theorem cert_config_362_d_red : (check cfgs[362]! md11 pow3).dReducible = true := by
  native_decide

end Batch
end Math
