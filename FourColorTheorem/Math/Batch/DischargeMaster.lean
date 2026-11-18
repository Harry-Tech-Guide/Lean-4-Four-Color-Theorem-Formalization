module

public import FourColorTheorem.Math.TestDischarging
public import FourColorTheorem.Math.U633Parser
public import FourColorTheorem.Math.Batch.DischargeDeg7
public import FourColorTheorem.Math.Batch.DischargeDeg8
public import FourColorTheorem.Math.Batch.DischargeDeg9
public import FourColorTheorem.Math.Batch.DischargeDeg10
public import FourColorTheorem.Math.Batch.DischargeDeg11

@[expose] public section

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math.Discharging

/-- Master theorem certifying that all RSST discharging trees (degrees 7 through 11)
    are formally verified against the unavoidable set and discharging rules. -/
theorem discharging_trees_verified : DischargingTreesVerified theUnavoidableSet.toList :=
  ⟨cert_deg7_verified, cert_deg8_verified, cert_deg9_verified, cert_deg10_verified, cert_deg11_verified⟩

end Math.Discharging
