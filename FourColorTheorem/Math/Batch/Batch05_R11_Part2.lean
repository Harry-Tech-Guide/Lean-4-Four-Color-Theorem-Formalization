import FourColorTheorem.Math.FastReducer

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 5: Ring 11 (Part 2)

This module certifies the D-reducibility of 6 configurations
from the RSST unavoidable set with ring size 11:
Configs 60, 69, 70, 71, 77, 81.

Every theorem is verified directly inside the Lean 4 kernel via `native_decide`,
depending solely on Lean's kernel reflection axiom `Lean.ofReduceBool`.
-/

private def pow3 := powers3 15
private def md11 := buildMData 11 pow3
private def cfgs := loadAll ()

/-- Config 60 (ring 11): D-reducible. -/
theorem cert_config_60_d_red : (check cfgs[60]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 69 (ring 11): D-reducible. -/
theorem cert_config_69_d_red : (check cfgs[69]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 70 (ring 11): D-reducible. -/
theorem cert_config_70_d_red : (check cfgs[70]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 71 (ring 11): D-reducible. -/
theorem cert_config_71_d_red : (check cfgs[71]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 77 (ring 11): D-reducible. -/
theorem cert_config_77_d_red : (check cfgs[77]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 81 (ring 11): D-reducible. -/
theorem cert_config_81_d_red : (check cfgs[81]! md11 pow3).dReducible = true := by
  native_decide

end Batch
end Math
