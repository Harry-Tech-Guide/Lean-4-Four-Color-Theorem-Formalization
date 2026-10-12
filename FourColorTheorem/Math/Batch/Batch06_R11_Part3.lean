import FourColorTheorem.Math.FastReducer

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 6: Ring 11 (Part 3)

This module certifies the D-reducibility of 6 configurations
from the RSST unavoidable set with ring size 11:
Configs 104, 114, 117, 119, 120, 129.

Every theorem is verified directly inside the Lean 4 kernel via `native_decide`,
depending solely on Lean's kernel reflection axiom `Lean.ofReduceBool`.
-/

private def pow3 := powers3 15
private def md11 := buildMData 11 pow3
private def cfgs := loadAll ()

/-- Config 104 (ring 11): D-reducible. -/
theorem cert_config_104_d_red : (check cfgs[104]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 114 (ring 11): D-reducible. -/
theorem cert_config_114_d_red : (check cfgs[114]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 117 (ring 11): D-reducible. -/
theorem cert_config_117_d_red : (check cfgs[117]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 119 (ring 11): D-reducible. -/
theorem cert_config_119_d_red : (check cfgs[119]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 120 (ring 11): D-reducible. -/
theorem cert_config_120_d_red : (check cfgs[120]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 129 (ring 11): D-reducible. -/
theorem cert_config_129_d_red : (check cfgs[129]! md11 pow3).dReducible = true := by
  native_decide

end Batch
end Math
