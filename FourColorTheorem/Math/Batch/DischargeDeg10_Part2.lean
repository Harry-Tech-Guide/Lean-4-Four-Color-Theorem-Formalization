import FourColorTheorem.Math.TestDischarging
import FourColorTheorem.Math.U633Parser
import FourColorTheorem.Math.KernelRfl
import FourColorTheorem.Math.Batch.DischargeDeg10_Defs

set_option maxHeartbeats 0

namespace Math.Discharging

theorem p_10_8 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_8 4105629843349963576032097773515384148851924615144855894615469360273363808232938740482721050688 235 3 25162 124830 [{ number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (advanceHints 2920 hs0_10) =
      (true, 404, advanceHints 5111 hs0_10) := by kernel_rfl

theorem p_10_9 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_9 4105629843349963576032097773515384148851924615144855894615469360273363808232938738489856225344 404 2 25162 124830 [{ number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (advanceHints 5111 hs0_10) =
      (true, 561, advanceHints 7721 hs0_10) := by kernel_rfl

end Math.Discharging
