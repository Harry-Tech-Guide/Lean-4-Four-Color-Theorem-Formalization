import FourColorTheorem.Math.FastReducer

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 3: Ring 10 (Part 2)

This module certifies the D-reducibility of the remaining 10 D-reducible configurations
from the RSST unavoidable set with ring size 10:
Configs 45, 47, 76, 110, 112, 324, 325, 328, 343, 566.

Every theorem is verified directly inside the Lean 4 kernel via `native_decide`,
depending solely on Lean's kernel reflection axiom `Lean.ofReduceBool`.
-/

private def pow3 := powers3 15
private def md10 := buildMData 10 pow3
private def cfgs := loadAll ()

/-- Config 45 (ring 10): D-reducible. -/
theorem cert_config_45_d_red : (check cfgs[45]! md10 pow3).dReducible = true := by
  native_decide

/-- Config 47 (ring 10): D-reducible. -/
theorem cert_config_47_d_red : (check cfgs[47]! md10 pow3).dReducible = true := by
  native_decide

/-- Config 76 (ring 10): D-reducible. -/
theorem cert_config_76_d_red : (check cfgs[76]! md10 pow3).dReducible = true := by
  native_decide

/-- Config 110 (ring 10): D-reducible. -/
theorem cert_config_110_d_red : (check cfgs[110]! md10 pow3).dReducible = true := by
  native_decide

/-- Config 112 (ring 10): D-reducible. -/
theorem cert_config_112_d_red : (check cfgs[112]! md10 pow3).dReducible = true := by
  native_decide

/-- Config 324 (ring 10): D-reducible. -/
theorem cert_config_324_d_red : (check cfgs[324]! md10 pow3).dReducible = true := by
  native_decide

/-- Config 325 (ring 10): D-reducible. -/
theorem cert_config_325_d_red : (check cfgs[325]! md10 pow3).dReducible = true := by
  native_decide

/-- Config 328 (ring 10): D-reducible. -/
theorem cert_config_328_d_red : (check cfgs[328]! md10 pow3).dReducible = true := by
  native_decide

/-- Config 343 (ring 10): D-reducible. -/
theorem cert_config_343_d_red : (check cfgs[343]! md10 pow3).dReducible = true := by
  native_decide

/-- Config 566 (ring 10): D-reducible. -/
theorem cert_config_566_d_red : (check cfgs[566]! md10 pow3).dReducible = true := by
  native_decide

end Batch
end Math
