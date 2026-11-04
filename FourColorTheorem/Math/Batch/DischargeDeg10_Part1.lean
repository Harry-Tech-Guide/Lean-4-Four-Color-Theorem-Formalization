import FourColorTheorem.Math.TestDischarging
import FourColorTheorem.Math.U633Parser
import FourColorTheorem.Math.KernelRfl
import FourColorTheorem.Math.Batch.DischargeDeg10_Defs

set_option maxHeartbeats 0

namespace Math.Discharging

theorem p_10_4 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_4 4105629843349963576032097773515384148851924615144855894615469360273363808232946898927718627264 6 4 1868362 7989150 [] (advanceHints 0 hs0_10) =
      (true, 93, advanceHints 1125 hs0_10) := by kernel_rfl

theorem p_10_5 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_5 4105629843349963576032097773515384148851924615144855894615469360273363808232946771384369805248 93 3 1868362 7989150 [] (advanceHints 1125 hs0_10) =
      (true, 232, advanceHints 2920 hs0_10) := by kernel_rfl

end Math.Discharging
