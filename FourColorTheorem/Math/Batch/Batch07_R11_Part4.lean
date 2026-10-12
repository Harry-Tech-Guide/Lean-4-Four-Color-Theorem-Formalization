import FourColorTheorem.Math.FastReducer

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 7: Ring 11 (Part 4)

This module certifies the D-reducibility of 6 configurations
from the RSST unavoidable set with ring size 11:
Configs 133, 201, 330, 332, 334, 336.

Every theorem is verified directly inside the Lean 4 kernel via `native_decide`,
depending solely on Lean's kernel reflection axiom `Lean.ofReduceBool`.
-/

private def pow3 := powers3 15
private def md11 := buildMData 11 pow3
private def cfgs := loadAll ()

/-- Config 133 (ring 11): D-reducible. -/
theorem cert_config_133_d_red : (check cfgs[133]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 201 (ring 11): D-reducible. -/
theorem cert_config_201_d_red : (check cfgs[201]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 330 (ring 11): D-reducible. -/
theorem cert_config_330_d_red : (check cfgs[330]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 332 (ring 11): D-reducible. -/
theorem cert_config_332_d_red : (check cfgs[332]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 334 (ring 11): D-reducible. -/
theorem cert_config_334_d_red : (check cfgs[334]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 336 (ring 11): D-reducible. -/
theorem cert_config_336_d_red : (check cfgs[336]! md11 pow3).dReducible = true := by
  native_decide

end Batch
end Math
