import FourColorTheorem.Math.FastReducer

namespace Math
namespace Batch

open FastReducer

/-!
# In-Kernel D-Reducibility Batch 10: Ring 11 (Part 7)

This module certifies the D-reducibility of the final 5 configurations
from the RSST unavoidable set with ring size 11:
Configs 568, 570, 571, 582, 621.

Every theorem is verified directly inside the Lean 4 kernel via `native_decide`,
depending solely on Lean's kernel reflection axiom `Lean.ofReduceBool`.
-/

private def pow3 := powers3 15
private def md11 := buildMData 11 pow3
private def cfgs := loadAll ()

/-- Config 568 (ring 11): D-reducible. -/
theorem cert_config_568_d_red : (check cfgs[568]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 570 (ring 11): D-reducible. -/
theorem cert_config_570_d_red : (check cfgs[570]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 571 (ring 11): D-reducible. -/
theorem cert_config_571_d_red : (check cfgs[571]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 582 (ring 11): D-reducible. -/
theorem cert_config_582_d_red : (check cfgs[582]! md11 pow3).dReducible = true := by
  native_decide

/-- Config 621 (ring 11): D-reducible. -/
theorem cert_config_621_d_red : (check cfgs[621]! md11 pow3).dReducible = true := by
  native_decide

end Batch
end Math
