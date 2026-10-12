import FourColorTheorem.Math.FastReducer

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 9: Ring 11 (Part 6)

This module certifies the D-reducibility of 5 configurations
from the RSST unavoidable set with ring size 11:
Configs 401, 404, 423, 424, 567.

Every theorem is verified directly inside the Lean 4 kernel via `native_decide`,
depending solely on Lean's kernel reflection axiom `Lean.ofReduceBool`.
-/

private def pow3 := powers3 15
private def md11 := buildMData 11 pow3
private def cfgs := loadAll ()

/-- Config 401 (ring 11): D-reducible. -/
theorem cert_config_401_d_red : (check cfgs[401]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 404 (ring 11): D-reducible. -/
theorem cert_config_404_d_red : (check cfgs[404]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 423 (ring 11): D-reducible. -/
theorem cert_config_423_d_red : (check cfgs[423]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 424 (ring 11): D-reducible. -/
theorem cert_config_424_d_red : (check cfgs[424]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 567 (ring 11): D-reducible. -/
theorem cert_config_567_d_red : (check cfgs[567]! md11 pow3).dReducible = true := by
  native_decide

end Batch
end Math
