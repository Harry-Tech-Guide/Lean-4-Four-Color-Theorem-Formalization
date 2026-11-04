import FourColorTheorem.Math.TestDischarging
import FourColorTheorem.Math.U633Parser
import FourColorTheorem.Math.KernelRfl
import FourColorTheorem.Math.Batch.DischargeDeg10_Defs

set_option maxHeartbeats 0

namespace Math.Discharging

theorem p_10_12 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_12 4105629843349963576032097773515384148851924615144855894615469360273363808232424762845920358464 564 2 458 1950 [{ number := 563, nolines := 2, conds := [(10, 30), (1, 30)] }, { number := 561, nolines := 2, conds := [(10, 30), (9, 30)] }] (advanceHints 7721 hs0_10) =
      (true, 637, advanceHints 8964 hs0_10) := by kernel_rfl

theorem p_10_13 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_13 4105629843349963576032097773515384148851924615144855894615469360273363808232424635302571536448 637 1 458 1950 [{ number := 563, nolines := 2, conds := [(10, 30), (1, 30)] }, { number := 561, nolines := 2, conds := [(10, 30), (9, 30)] }] (advanceHints 8964 hs0_10) =
      (true, 848, advanceHints 10785 hs0_10) := by kernel_rfl

end Math.Discharging
