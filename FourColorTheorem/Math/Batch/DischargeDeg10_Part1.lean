import FourColorTheorem.Math.TestDischarging
import FourColorTheorem.Math.U633Parser
import FourColorTheorem.Math.DischargingSplit
import FourColorTheorem.Math.Batch.DischargeDeg10_Defs

set_option maxHeartbeats 0
set_option maxRecDepth 10000000

namespace Math.Discharging

theorem p_10_6 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_6 4105629843349963576032097773515384148851924615144855894615469360273363808232946898857925408704 8 6 5471240778 32723560350 [] (hintStreamAt hints_10 0) =
      (true, 9, hintStreamAt hints_10 67) := by kernel_rfl

theorem p_10_9 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_9 4105629843349963576032097773515384148851924615144855894615469360273363808232946898826770116672 12 6 4397498954 32723560350 [{ number := 11, nolines := 6, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (6, 30), (1, 30)] }, { number := 9, nolines := 6, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (6, 30), (5, 30)] }] (hintStreamAt hints_10 67) =
      (true, 17, hintStreamAt hints_10 212) := by kernel_rfl

theorem p_10_10 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_10 4105629843349963576032097773515384148851924615144855894615469360273363808232946898826283577408 17 5 4397498954 32723560350 [{ number := 11, nolines := 6, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (6, 30), (1, 30)] }, { number := 9, nolines := 6, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (6, 30), (5, 30)] }] (hintStreamAt hints_10 212) =
      (true, 22, hintStreamAt hints_10 341) := by kernel_rfl

theorem p_10_14 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_14 4105629843349963576032097773515384148851924615144855894615469360273363808232946896865043804224 26 6 4380721738 32723560350 [{ number := 24, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (1, 30)] }, { number := 22, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (6, 30)] }] (hintStreamAt hints_10 341) =
      (true, 31, hintStreamAt hints_10 465) := by kernel_rfl

theorem p_10_16 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_16 4105629843349963576032097773515384148851924615144855894615469360273363808232946896864557002816 32 6 3306979914 32723560350 [{ number := 31, nolines := 6, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (5, 30), (4, 30)] }, { number := 24, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (1, 30)] }, { number := 22, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (6, 30)] }] (hintStreamAt hints_10 465) =
      (true, 35, hintStreamAt hints_10 531) := by kernel_rfl

theorem p_10_17 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_17 4105629843349963576032097773515384148851924615144855894615469360273363808232946896864549400640 35 5 3306979914 32723560350 [{ number := 31, nolines := 6, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (5, 30), (4, 30)] }, { number := 24, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (1, 30)] }, { number := 22, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (6, 30)] }] (hintStreamAt hints_10 531) =
      (true, 38, hintStreamAt hints_10 663) := by kernel_rfl

theorem p_10_20 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_20 4105629843349963576032097773515384148851924615144855894615469360273363808232946896833905168448 41 5 68977226 511305630 [{ number := 40, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (2, 30)] }, { number := 38, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (5, 30)] }, { number := 24, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (1, 30)] }, { number := 22, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (6, 30)] }] (hintStreamAt hints_10 663) =
      (true, 42, hintStreamAt hints_10 742) := by kernel_rfl

theorem p_10_23 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_23 4105629843349963576032097773515384148851924615144855894615469360273363808232946888037317742656 45 5 119308874 477751198 [{ number := 44, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (3, 30)] }, { number := 42, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (4, 30)] }, { number := 40, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (2, 30)] }, { number := 38, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (5, 30)] }, { number := 24, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (1, 30)] }, { number := 22, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (6, 30)] }] (hintStreamAt hints_10 742) =
      (true, 46, hintStreamAt hints_10 796) := by kernel_rfl

theorem p_10_27 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_27 4105629843349963576032097773515384148851924615144855894615469360273363808230128646221281366080 51 5 169640522 477751198 [{ number := 50, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (9, 28)] }, { number := 48, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (8, 28)] }, { number := 46, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (7, 28)] }, { number := 44, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (3, 30)] }, { number := 42, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (4, 30)] }, { number := 40, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (2, 30)] }, { number := 38, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (5, 30)] }, { number := 24, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (1, 30)] }, { number := 22, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (6, 30)] }] (hintStreamAt hints_10 835) =
      (true, 52, hintStreamAt hints_10 888) := by kernel_rfl

theorem p_10_32 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_32 4105629843349963576032097773515384148851924609298849345291848456743866265425576259859207426112 60 4 303858250 477751198 [{ number := 58, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (17, 28)] }, { number := 54, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (16, 28)] }, { number := 52, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (10, 28)] }, { number := 50, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (9, 28)] }, { number := 48, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (8, 28)] }, { number := 46, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (7, 28)] }, { number := 44, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (3, 30)] }, { number := 42, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (4, 30)] }, { number := 40, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (2, 30)] }, { number := 38, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (5, 30)] }, { number := 24, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (1, 30)] }, { number := 22, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (7, 30), (6, 30)] }] (hintStreamAt hints_10 975) =
      (true, 93, hintStreamAt hints_10 1125) := by kernel_rfl

theorem p_10_37 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_37 4105629843349963576032097773515384148851924615144855894615469360273363808232946771314559807552 98 6 4380459594 32723560350 [{ number := 95, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (1, 30)] }, { number := 93, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (7, 30)] }] (hintStreamAt hints_10 1125) =
      (true, 101, hintStreamAt hints_10 1187) := by kernel_rfl

theorem p_10_39 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_39 4105629843349963576032097773515384148851924615144855894615469360273363808232946771314073006144 102 6 3306717770 32723560350 [{ number := 101, nolines := 6, conds := [(10, 30), (9, 30), (8, 30), (6, 30), (5, 30), (4, 30)] }, { number := 95, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (1, 30)] }, { number := 93, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (7, 30)] }] (hintStreamAt hints_10 1187) =
      (true, 103, hintStreamAt hints_10 1253) := by kernel_rfl

theorem p_10_41 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_41 4105629843349963576032097773515384148851924615144855894615469360273363808232946771314065399872 104 6 2232975946 32723560350 [{ number := 103, nolines := 6, conds := [(10, 30), (9, 30), (8, 30), (6, 30), (5, 30), (3, 30)] }, { number := 101, nolines := 6, conds := [(10, 30), (9, 30), (8, 30), (6, 30), (5, 30), (4, 30)] }, { number := 95, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (1, 30)] }, { number := 93, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (7, 30)] }] (hintStreamAt hints_10 1253) =
      (true, 105, hintStreamAt hints_10 1321) := by kernel_rfl

theorem p_10_50 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_50 4105629843349963576032097773515384148851924615144855894615469360273363808232946771314065281088 105 5 2232975946 32723560350 [{ number := 103, nolines := 6, conds := [(10, 30), (9, 30), (8, 30), (6, 30), (5, 30), (3, 30)] }, { number := 101, nolines := 6, conds := [(10, 30), (9, 30), (8, 30), (6, 30), (5, 30), (4, 30)] }, { number := 95, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (1, 30)] }, { number := 93, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (7, 30)] }] (hintStreamAt hints_10 1333) =
      (true, 106, hintStreamAt hints_10 1479) := by kernel_rfl

theorem p_10_53 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_53 4105629843349963576032097773515384148851924615144855894615469360273363808232946771283421032512 108 6 3289940554 32723560350 [{ number := 106, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (6, 30), (5, 30)] }, { number := 95, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (1, 30)] }, { number := 93, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (7, 30)] }] (hintStreamAt hints_10 1479) =
      (true, 111, hintStreamAt hints_10 1536) := by kernel_rfl

theorem p_10_55 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_55 4105629843349963576032097773515384148851924615144855894615469360273363808232946771283413426240 112 6 2216198730 32723560350 [{ number := 111, nolines := 6, conds := [(10, 30), (9, 30), (8, 30), (6, 30), (4, 30), (3, 30)] }, { number := 106, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (6, 30), (5, 30)] }, { number := 95, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (1, 30)] }, { number := 93, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (7, 30)] }] (hintStreamAt hints_10 1536) =
      (true, 113, hintStreamAt hints_10 1578) := by kernel_rfl

theorem p_10_57 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_57 4105629843349963576032097773515384148851924615144855894615469360273363808232946771283379753024 114 6 4363682378 30576076702 [{ number := 113, nolines := 6, conds := [(10, 30), (9, 30), (8, 30), (6, 30), (4, 30), (2, 30)] }, { number := 111, nolines := 6, conds := [(10, 30), (9, 30), (8, 30), (6, 30), (4, 30), (3, 30)] }, { number := 106, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (6, 30), (5, 30)] }, { number := 95, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (1, 30)] }, { number := 93, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (7, 30)] }] (hintStreamAt hints_10 1578) =
      (true, 115, hintStreamAt hints_10 1634) := by kernel_rfl

theorem p_10_60 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_60 4105629843349963576032097773515384148851924615144855894615469360273363808232938888059450298432 119 5 8658649674 30576076702 [{ number := 117, nolines := 6, conds := [(10, 30), (9, 30), (8, 30), (6, 30), (4, 30), (6, 28)] }, { number := 115, nolines := 6, conds := [(10, 30), (9, 30), (8, 30), (6, 30), (4, 30), (4, 28)] }, { number := 113, nolines := 6, conds := [(10, 30), (9, 30), (8, 30), (6, 30), (4, 30), (2, 30)] }, { number := 111, nolines := 6, conds := [(10, 30), (9, 30), (8, 30), (6, 30), (4, 30), (3, 30)] }, { number := 106, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (6, 30), (5, 30)] }, { number := 95, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (1, 30)] }, { number := 93, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (7, 30)] }] (hintStreamAt hints_10 1662) =
      (true, 136, hintStreamAt hints_10 1810) := by kernel_rfl

theorem cbp_10_1 :
    evalCBPrefix 10 2 (childCBState cb_10_70) (hintStreamAt hints_10 1817) =
      (true, hintStreamAt hints_10 1928) := by kernel_rfl

theorem cbp_10_2 :
    evalCBState 10 (advanceCBState 2 (childCBState cb_10_70)) (hintStreamAt hints_10 1928) =
      (true, hintStreamAt hints_10 1997) := by kernel_rfl

theorem cbp_10_4 :
    evalCBState 10 (advanceCBState 1 cb_10_70) (hintStreamAt hints_10 1997) =
      (true, hintStreamAt hints_10 2095) := by kernel_rfl

theorem p_10_72 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_72 4105629843349963576032097773515384148851924615144855894615469360273363808232946771282926886976 141 5 35160650 511305630 [{ number := 140, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (6, 30), (3, 30)] }, { number := 136, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (6, 30), (4, 30)] }, { number := 106, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (6, 30), (5, 30)] }, { number := 95, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (1, 30)] }, { number := 93, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (7, 30)] }] (hintStreamAt hints_10 2140) =
      (true, 142, hintStreamAt hints_10 2215) := by kernel_rfl

theorem p_10_73 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_73 4105629843349963576032097773515384148851924615144855894615469360273363808232946771282926768192 142 4 35160650 511305630 [{ number := 140, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (6, 30), (3, 30)] }, { number := 136, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (6, 30), (4, 30)] }, { number := 106, nolines := 5, conds := [(10, 30), (9, 30), (8, 30), (6, 30), (5, 30)] }, { number := 95, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (1, 30)] }, { number := 93, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (7, 30)] }] (hintStreamAt hints_10 2215) =
      (true, 155, hintStreamAt hints_10 2356) := by kernel_rfl

theorem p_10_77 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_77 4105629843349963576032097773515384148851924615144855894615469360273363808232946769321694859328 159 5 68452938 511305630 [{ number := 157, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (2, 30)] }, { number := 155, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (6, 30)] }, { number := 95, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (1, 30)] }, { number := 93, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (7, 30)] }] (hintStreamAt hints_10 2356) =
      (true, 160, hintStreamAt hints_10 2467) := by kernel_rfl

theorem p_10_78 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_78 4105629843349963576032097773515384148851924615144855894615469360273363808232946769321208320064 160 4 68452938 511305630 [{ number := 157, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (2, 30)] }, { number := 155, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (6, 30)] }, { number := 95, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (1, 30)] }, { number := 93, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (7, 30)] }] (hintStreamAt hints_10 2467) =
      (true, 165, hintStreamAt hints_10 2558) := by kernel_rfl

theorem p_10_88 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_88 4105629843349963576032097773515384148851913390812281193280466932206190210503816381184161878080 182 4 7373386 386974 [{ number := 181, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (19, 28)] }, { number := 179, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (18, 28)] }, { number := 177, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (10, 28)] }, { number := 175, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (9, 28)] }, { number := 173, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (8, 28)] }, { number := 171, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (4, 24)] }, { number := 169, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (4, 1)] }, { number := 167, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (3, 30)] }, { number := 165, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (5, 30)] }, { number := 157, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (2, 30)] }, { number := 155, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (6, 30)] }, { number := 95, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (1, 30)] }, { number := 93, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (7, 30)] }] (hintStreamAt hints_10 2685) =
      (true, 183, hintStreamAt hints_10 2739) := by kernel_rfl

theorem p_10_91 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_91 4105629843349963576032097773515384148851924241000436737903731534306292908112997001603057979456 186 4 4227658 7989150 [{ number := 185, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (17, 28)] }, { number := 181, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (19, 28)] }, { number := 179, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (18, 28)] }, { number := 177, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (10, 28)] }, { number := 175, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (9, 28)] }, { number := 173, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (8, 28)] }, { number := 171, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (4, 24)] }, { number := 169, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (4, 1)] }, { number := 167, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (3, 30)] }, { number := 165, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (5, 30)] }, { number := 157, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (2, 30)] }, { number := 155, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (6, 30)] }, { number := 95, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (1, 30)] }, { number := 93, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (7, 30)] }] (hintStreamAt hints_10 2767) =
      (true, 219, hintStreamAt hints_10 2909) := by kernel_rfl

theorem p_10_92 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_92 4105629843349963576032097773515384148851924241000436737903731532008676195199331211390283419712 219 3 4227658 7989150 [{ number := 185, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (17, 28)] }, { number := 181, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (19, 28)] }, { number := 179, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (18, 28)] }, { number := 177, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (10, 28)] }, { number := 175, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (9, 28)] }, { number := 173, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (8, 28)] }, { number := 171, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (4, 24)] }, { number := 169, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (4, 1)] }, { number := 167, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (3, 30)] }, { number := 165, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (5, 30)] }, { number := 157, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (2, 30)] }, { number := 155, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (6, 30)] }, { number := 95, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (1, 30)] }, { number := 93, nolines := 4, conds := [(10, 30), (9, 30), (8, 30), (7, 30)] }] (hintStreamAt hints_10 2909) =
      (true, 232, hintStreamAt hints_10 2920) := by kernel_rfl

theorem p_10_100 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_100 4105629843349963576032097773515384148851924615144855894615469360273363808232938608539748393024 242 6 2199151178 32723560350 [{ number := 240, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (5, 30), (7, 30)] }, { number := 238, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (5, 30), (4, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 2920) =
      (true, 243, hintStreamAt hints_10 2989) := by kernel_rfl

theorem p_10_106 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_106 4105629843349963576032097773515384148851924615144855894615469360273363808232938608539748274240 243 5 2199151178 32723560350 [{ number := 240, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (5, 30), (7, 30)] }, { number := 238, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (5, 30), (4, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 2993) =
      (true, 244, hintStreamAt hints_10 3124) := by kernel_rfl

theorem p_10_107 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_107 4105629843349963576032097773515384148851924615144855894615469360273363808232938608539748274240 243 5 2199151178 32723560350 [{ number := 240, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (5, 30), (7, 30)] }, { number := 238, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (5, 30), (4, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 3124) =
      (true, 244, hintStreamAt hints_10 3177) := by kernel_rfl

theorem cbp_10_6 :
    evalCBPrefix 10 2 (childCBState cb_10_117) (hintStreamAt hints_10 3197) =
      (true, hintStreamAt hints_10 3316) := by kernel_rfl

theorem cbp_10_7 :
    evalCBState 10 (advanceCBState 2 (childCBState cb_10_117)) (hintStreamAt hints_10 3316) =
      (true, hintStreamAt hints_10 3381) := by kernel_rfl

theorem cbp_10_9 :
    evalCBState 10 (advanceCBState 1 cb_10_117) (hintStreamAt hints_10 3381) =
      (true, hintStreamAt hints_10 3395) := by kernel_rfl

theorem p_10_125 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_125 4105629843349963576032097773515384148851924615144855894615469360273363808232902586858410094656 259 5 151806538 477751198 [{ number := 258, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (3, 30), (7, 28)] }, { number := 256, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (3, 30), (6, 24)] }, { number := 254, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (3, 30), (3, 24)] }, { number := 252, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (3, 30), (2, 28)] }, { number := 250, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (3, 30), (4, 30)] }, { number := 247, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (5, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 3465) =
      (true, 260, hintStreamAt hints_10 3500) := by kernel_rfl

theorem p_10_127 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_127 4105629843349963576032097773515384148851924615144855894615469360273363808230128369487949869120 261 5 168583754 477751198 [{ number := 260, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (3, 30), (9, 28)] }, { number := 258, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (3, 30), (7, 28)] }, { number := 256, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (3, 30), (6, 24)] }, { number := 254, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (3, 30), (3, 24)] }, { number := 252, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (3, 30), (2, 28)] }, { number := 250, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (3, 30), (4, 30)] }, { number := 247, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (5, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 3500) =
      (true, 262, hintStreamAt hints_10 3535) := by kernel_rfl

theorem p_10_131 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_131 4105629843349963576032097773515384148851900669902029865101466887333406247976413023611938943040 268 4 319578698 477751198 [{ number := 264, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (3, 30), (18, 28)] }, { number := 262, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (3, 30), (10, 28)] }, { number := 260, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (3, 30), (9, 28)] }, { number := 258, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (3, 30), (7, 28)] }, { number := 256, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (3, 30), (6, 24)] }, { number := 254, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (3, 30), (3, 24)] }, { number := 252, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (3, 30), (2, 28)] }, { number := 250, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (3, 30), (4, 30)] }, { number := 247, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (5, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 3587) =
      (true, 313, hintStreamAt hints_10 3735) := by kernel_rfl

theorem p_10_134 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_134 4105629843349963576032097773515384148851924615144855894615469360273363808232938740450500902976 315 5 34103882 410642334 [{ number := 313, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (3, 30)] }, { number := 247, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (5, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 3735) =
      (true, 316, hintStreamAt hints_10 3756) := by kernel_rfl

theorem p_10_136 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_136 4105629843349963576032097773515384148851924615144855894615469360273363808232938740450450497600 317 5 67658314 477751198 [{ number := 316, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (2, 24)] }, { number := 313, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (3, 30)] }, { number := 247, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (5, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 3756) =
      (true, 318, hintStreamAt hints_10 3800) := by kernel_rfl

theorem p_10_138 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_138 4105629843349963576032097773515384148851924615144855894615469360273363808232938740037714206784 319 5 101212746 410642334 [{ number := 318, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (4, 28)] }, { number := 316, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (2, 24)] }, { number := 313, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (3, 30)] }, { number := 247, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (5, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 3800) =
      (true, 320, hintStreamAt hints_10 3839) := by kernel_rfl

theorem p_10_143 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_143 4105629843349963576032097773515384148851924615144855894615469360273363808200188439165223067712 327 5 151544394 477751198 [{ number := 326, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (10, 28)] }, { number := 324, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (9, 24)] }, { number := 322, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (7, 28)] }, { number := 320, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (6, 24)] }, { number := 318, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (4, 28)] }, { number := 316, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (2, 24)] }, { number := 313, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (3, 30)] }, { number := 247, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (5, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 3902) =
      (true, 332, hintStreamAt hints_10 3996) := by kernel_rfl

theorem p_10_145 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_145 4105629843349963576032097773515384148851924615144855894615469360273363808200152410230765150272 333 5 101212746 477751198 [{ number := 332, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (9, 28)] }, { number := 326, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (10, 28)] }, { number := 324, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (9, 24)] }, { number := 322, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (7, 28)] }, { number := 320, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (6, 24)] }, { number := 318, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (4, 28)] }, { number := 316, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (2, 24)] }, { number := 313, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (3, 30)] }, { number := 247, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (5, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 3996) =
      (true, 334, hintStreamAt hints_10 4057) := by kernel_rfl

theorem p_10_152 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_152 4105629843349963576032097773515384148851900669810686012768285454911013622618045398066275835968 346 4 319316554 477751198 [{ number := 342, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (18, 28)] }, { number := 338, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (15, 28)] }, { number := 336, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (11, 30)] }, { number := 334, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (6, 28)] }, { number := 332, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (9, 28)] }, { number := 326, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (10, 28)] }, { number := 324, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (9, 24)] }, { number := 322, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (7, 28)] }, { number := 320, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (6, 24)] }, { number := 318, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (4, 28)] }, { number := 316, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (2, 30), (2, 24)] }, { number := 313, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (3, 30)] }, { number := 247, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (5, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 4185) =
      (true, 375, hintStreamAt hints_10 4330) := by kernel_rfl

theorem p_10_156 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_156 4105629843349963576032097773515384148851924615144855894615469360273363808232938608508988035136 379 5 68182602 410642334 [{ number := 378, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (4, 30), (7, 30)] }, { number := 375, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (2, 30)] }, { number := 313, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (3, 30)] }, { number := 247, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (5, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 4330) =
      (true, 380, hintStreamAt hints_10 4382) := by kernel_rfl

theorem p_10_158 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_158 4105629843349963576032097773515384148851924615144855894615469360273363808232938608096369184832 381 5 101737034 410642334 [{ number := 380, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (4, 30), (4, 24)] }, { number := 378, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (4, 30), (7, 30)] }, { number := 375, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (2, 30)] }, { number := 313, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (3, 30)] }, { number := 247, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (5, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 4382) =
      (true, 382, hintStreamAt hints_10 4434) := by kernel_rfl

theorem p_10_169 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_169 4105629843349963576032097773515384148851924615144855894615469360273363808126365425277323186240 387 5 185623114 511305630 [{ number := 386, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (4, 30), (10, 28)] }, { number := 384, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (4, 30), (9, 28)] }, { number := 382, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (4, 30), (6, 24)] }, { number := 380, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (4, 30), (4, 24)] }, { number := 378, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (4, 30), (7, 30)] }, { number := 375, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (2, 30)] }, { number := 313, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (3, 30)] }, { number := 247, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (5, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 4488) =
      (true, 388, hintStreamAt hints_10 4610) := by kernel_rfl

theorem p_10_170 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_170 4105629843349963576032097773515384148851924615144855894615469360273363805986543112727015198784 388 4 185623114 511305630 [{ number := 386, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (4, 30), (10, 28)] }, { number := 384, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (4, 30), (9, 28)] }, { number := 382, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (4, 30), (6, 24)] }, { number := 380, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (4, 30), (4, 24)] }, { number := 378, nolines := 5, conds := [(10, 30), (9, 30), (6, 30), (4, 30), (7, 30)] }, { number := 375, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (2, 30)] }, { number := 313, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (3, 30)] }, { number := 247, nolines := 4, conds := [(10, 30), (9, 30), (6, 30), (5, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 4645) =
      (true, 403, hintStreamAt hints_10 4719) := by kernel_rfl

theorem cbp_10_11 :
    evalCBPrefix 10 11 cb_10_178 (hintStreamAt hints_10 4725) =
      (true, hintStreamAt hints_10 4875) := by kernel_rfl

theorem cbp_10_12 :
    evalCBState 10 (advanceCBState 11 cb_10_178) (hintStreamAt hints_10 4875) =
      (true, hintStreamAt hints_10 4907) := by kernel_rfl

theorem cbp_10_14 :
    evalCBPrefix 10 2 (childCBState cb_10_179) (hintStreamAt hints_10 4907) =
      (true, hintStreamAt hints_10 5032) := by kernel_rfl

theorem cbp_10_15 :
    evalCBState 10 (advanceCBState 2 (childCBState cb_10_179)) (hintStreamAt hints_10 5032) =
      (true, hintStreamAt hints_10 5097) := by kernel_rfl

theorem cbp_10_17 :
    evalCBState 10 (advanceCBState 1 cb_10_179) (hintStreamAt hints_10 5097) =
      (true, hintStreamAt hints_10 5111) := by kernel_rfl

theorem p_10_185 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_185 4105629843349963576032097773515384148851924615144855894615469360273363808232938738488757829696 410 6 2182365770 30576076702 [{ number := 406, nolines := 3, conds := [(10, 30), (9, 30), (3, 30)] }, { number := 404, nolines := 3, conds := [(10, 30), (9, 30), (6, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 5111) =
      (true, 411, hintStreamAt hints_10 5153) := by kernel_rfl

theorem p_10_187 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_187 4105629843349963576032097773515384148851924615144855894615469360273363808232938738488724168768 412 6 4329849418 30576076702 [{ number := 411, nolines := 6, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (2, 30), (2, 28)] }, { number := 406, nolines := 3, conds := [(10, 30), (9, 30), (3, 30)] }, { number := 404, nolines := 3, conds := [(10, 30), (9, 30), (6, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 5153) =
      (true, 413, hintStreamAt hints_10 5190) := by kernel_rfl

theorem p_10_189 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_189 4105629843349963576032097773515384148851924615144855894615469360273363808232938738486140477504 414 6 5403591242 30576076702 [{ number := 413, nolines := 6, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (2, 30), (4, 28)] }, { number := 411, nolines := 6, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (2, 30), (2, 28)] }, { number := 406, nolines := 3, conds := [(10, 30), (9, 30), (3, 30)] }, { number := 404, nolines := 3, conds := [(10, 30), (9, 30), (6, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 5190) =
      (true, 415, hintStreamAt hints_10 5233) := by kernel_rfl

theorem p_10_194 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_194 4105629843349963576032097773515384148851924615144855894615469360273363805986543112384424452160 423 5 11846042186 32723560350 [{ number := 421, nolines := 6, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (2, 30), (10, 28)] }, { number := 419, nolines := 6, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (2, 30), (9, 28)] }, { number := 417, nolines := 6, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (2, 30), (7, 30)] }, { number := 415, nolines := 6, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (2, 30), (5, 28)] }, { number := 413, nolines := 6, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (2, 30), (4, 28)] }, { number := 411, nolines := 6, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (2, 30), (2, 28)] }, { number := 406, nolines := 3, conds := [(10, 30), (9, 30), (3, 30)] }, { number := 404, nolines := 3, conds := [(10, 30), (9, 30), (6, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 5323) =
      (true, 432, hintStreamAt hints_10 5472) := by kernel_rfl

theorem p_10_197 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_197 4105629843349963576032097773515384148851924615144855894615469360273363808232938606547328831552 435 5 68436554 477751198 [{ number := 434, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (7, 30)] }, { number := 432, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (2, 30)] }, { number := 406, nolines := 3, conds := [(10, 30), (9, 30), (3, 30)] }, { number := 404, nolines := 3, conds := [(10, 30), (9, 30), (6, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 5472) =
      (true, 436, hintStreamAt hints_10 5534) := by kernel_rfl

theorem p_10_199 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_199 4105629843349963576032097773515384148851924615144855894615469360273363808232938606544745140288 437 5 85213770 477751198 [{ number := 436, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (4, 28)] }, { number := 434, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (7, 30)] }, { number := 432, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (2, 30)] }, { number := 406, nolines := 3, conds := [(10, 30), (9, 30), (3, 30)] }, { number := 404, nolines := 3, conds := [(10, 30), (9, 30), (6, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 5534) =
      (true, 438, hintStreamAt hints_10 5589) := by kernel_rfl

theorem p_10_201 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_201 4105629843349963576032097773515384148851924615144855894615469360273363808232902577719808888896 439 5 152322634 477751198 [{ number := 438, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (5, 28)] }, { number := 436, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (4, 28)] }, { number := 434, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (7, 30)] }, { number := 432, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (2, 30)] }, { number := 406, nolines := 3, conds := [(10, 30), (9, 30), (3, 30)] }, { number := 404, nolines := 3, conds := [(10, 30), (9, 30), (6, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 5589) =
      (true, 440, hintStreamAt hints_10 5651) := by kernel_rfl

theorem p_10_203 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_203 4105629843349963576032097773515384148851924615144855894615469360273363808230128360349348663360 441 5 169099850 477751198 [{ number := 440, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (9, 28)] }, { number := 438, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (5, 28)] }, { number := 436, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (4, 28)] }, { number := 434, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (7, 30)] }, { number := 432, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (2, 30)] }, { number := 406, nolines := 3, conds := [(10, 30), (9, 30), (3, 30)] }, { number := 404, nolines := 3, conds := [(10, 30), (9, 30), (6, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 5651) =
      (true, 442, hintStreamAt hints_10 5713) := by kernel_rfl

theorem p_10_205 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_205 4105629843349963576032097773515384148851924615144855894615469360273362901505787690257689612352 443 5 219431498 477751198 [{ number := 442, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (10, 28)] }, { number := 440, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (9, 28)] }, { number := 438, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (5, 28)] }, { number := 436, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (4, 28)] }, { number := 434, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (7, 30)] }, { number := 432, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (2, 30)] }, { number := 406, nolines := 3, conds := [(10, 30), (9, 30), (3, 30)] }, { number := 404, nolines := 3, conds := [(10, 30), (9, 30), (6, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 5713) =
      (true, 444, hintStreamAt hints_10 5771) := by kernel_rfl

theorem p_10_208 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_208 4105629843349963576032097773515384148851924615144833593870270829649672211233955096593573351488 448 4 236208714 477751198 [{ number := 444, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (13, 28)] }, { number := 442, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (10, 28)] }, { number := 440, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (9, 28)] }, { number := 438, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (5, 28)] }, { number := 436, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (4, 28)] }, { number := 434, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (7, 30)] }, { number := 432, nolines := 5, conds := [(10, 30), (9, 30), (4, 30), (5, 30), (2, 30)] }, { number := 406, nolines := 3, conds := [(10, 30), (9, 30), (3, 30)] }, { number := 404, nolines := 3, conds := [(10, 30), (9, 30), (6, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 5822) =
      (true, 481, hintStreamAt hints_10 5972) := by kernel_rfl

theorem p_10_210 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_210 4105629843349963576032097773515384148851924615144855894615469360273363808232938738457619316800 482 4 541258 7464862 [{ number := 481, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (5, 30)] }, { number := 406, nolines := 3, conds := [(10, 30), (9, 30), (3, 30)] }, { number := 404, nolines := 3, conds := [(10, 30), (9, 30), (6, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 5972) =
      (true, 483, hintStreamAt hints_10 6020) := by kernel_rfl

theorem cbp_10_19 :
    evalCBPrefix 10 9 cb_10_219 (hintStreamAt hints_10 6026) =
      (true, hintStreamAt hints_10 6147) := by kernel_rfl

theorem cbp_10_20 :
    evalCBState 10 (advanceCBState 9 cb_10_219) (hintStreamAt hints_10 6147) =
      (true, hintStreamAt hints_10 6195) := by kernel_rfl

theorem p_10_232 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_232 4105629843349963576032097773515384148851924615144855894615469360273363808204836144841029328960 493 5 35406410 503703454 [{ number := 491, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (10, 24)] }, { number := 489, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (9, 24)] }, { number := 487, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (7, 24)] }, { number := 485, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (4, 24)] }, { number := 483, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (2, 28)] }, { number := 481, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (5, 30)] }, { number := 406, nolines := 3, conds := [(10, 30), (9, 30), (3, 30)] }, { number := 404, nolines := 3, conds := [(10, 30), (9, 30), (6, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 6318) =
      (true, 494, hintStreamAt hints_10 6464) := by kernel_rfl

theorem cbp_10_22 :
    evalCBPrefix 10 2 (childCBState cb_10_241) (hintStreamAt hints_10 6490) =
      (true, hintStreamAt hints_10 6609) := by kernel_rfl

theorem cbp_10_23 :
    evalCBState 10 (advanceCBState 2 (childCBState cb_10_241)) (hintStreamAt hints_10 6609) =
      (true, hintStreamAt hints_10 6674) := by kernel_rfl

theorem cbp_10_25 :
    evalCBState 10 (advanceCBState 1 cb_10_241) (hintStreamAt hints_10 6674) =
      (true, hintStreamAt hints_10 6688) := by kernel_rfl

theorem p_10_244 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_244 4105629843349963576032097773515384148851924615144855894615469360273363808204764109237223956544 498 4 541258 7989150 [{ number := 497, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (9, 28)] }, { number := 495, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (7, 1)] }, { number := 491, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (10, 24)] }, { number := 489, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (9, 24)] }, { number := 487, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (7, 24)] }, { number := 485, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (4, 24)] }, { number := 483, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (2, 28)] }, { number := 481, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (5, 30)] }, { number := 406, nolines := 3, conds := [(10, 30), (9, 30), (3, 30)] }, { number := 404, nolines := 3, conds := [(10, 30), (9, 30), (6, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 6716) =
      (true, 503, hintStreamAt hints_10 6846) := by kernel_rfl

theorem cbp_10_27 :
    evalCBPrefix 10 2 (childCBState cb_10_253) (hintStreamAt hints_10 6850) =
      (true, hintStreamAt hints_10 6958) := by kernel_rfl

theorem cbp_10_28 :
    evalCBState 10 (advanceCBState 2 (childCBState cb_10_253)) (hintStreamAt hints_10 6958) =
      (true, hintStreamAt hints_10 7026) := by kernel_rfl

theorem cbp_10_30 :
    evalCBState 10 (advanceCBState 1 cb_10_253) (hintStreamAt hints_10 7026) =
      (true, hintStreamAt hints_10 7120) := by kernel_rfl

theorem p_10_255 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_255 4105629843349963576032097773515384148851924615144855894615469360273363808200152405626610520128 506 4 1851978 911262 [{ number := 505, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (10, 28)] }, { number := 503, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (2, 30)] }, { number := 497, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (9, 28)] }, { number := 495, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (7, 1)] }, { number := 491, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (10, 24)] }, { number := 489, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (9, 24)] }, { number := 487, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (7, 24)] }, { number := 485, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (4, 24)] }, { number := 483, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (2, 28)] }, { number := 481, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (5, 30)] }, { number := 406, nolines := 3, conds := [(10, 30), (9, 30), (3, 30)] }, { number := 404, nolines := 3, conds := [(10, 30), (9, 30), (6, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 7128) =
      (true, 507, hintStreamAt hints_10 7232) := by kernel_rfl

theorem p_10_256 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_256 4105629843349963576032097773515384148851924615144855894615469360273363808200152414422703542336 507 3 1851978 911262 [{ number := 505, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (10, 28)] }, { number := 503, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (2, 30)] }, { number := 497, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (9, 28)] }, { number := 495, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (7, 1)] }, { number := 491, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (10, 24)] }, { number := 489, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (9, 24)] }, { number := 487, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (7, 24)] }, { number := 485, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (4, 24)] }, { number := 483, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (2, 28)] }, { number := 481, nolines := 4, conds := [(10, 30), (9, 30), (4, 30), (5, 30)] }, { number := 406, nolines := 3, conds := [(10, 30), (9, 30), (3, 30)] }, { number := 404, nolines := 3, conds := [(10, 30), (9, 30), (6, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 7232) =
      (true, 528, hintStreamAt hints_10 7352) := by kernel_rfl

theorem p_10_263 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_263 4105629843349963576032097773515384148851924615144855894615469360273363808230200444330575159360 538 4 2630218 7464862 [{ number := 537, nolines := 4, conds := [(10, 30), (9, 30), (2, 30), (9, 24)] }, { number := 535, nolines := 4, conds := [(10, 30), (9, 30), (2, 30), (7, 24)] }, { number := 533, nolines := 4, conds := [(10, 30), (9, 30), (2, 30), (2, 24)] }, { number := 530, nolines := 3, conds := [(10, 30), (9, 30), (5, 30)] }, { number := 528, nolines := 3, conds := [(10, 30), (9, 30), (4, 30)] }, { number := 406, nolines := 3, conds := [(10, 30), (9, 30), (3, 30)] }, { number := 404, nolines := 3, conds := [(10, 30), (9, 30), (6, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 7426) =
      (true, 539, hintStreamAt hints_10 7519) := by kernel_rfl

theorem p_10_266 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_266 4105629843349963576032097773515384148851924615144855894615469360273363808200224467618611085376 542 4 117973578 477226910 [{ number := 539, nolines := 4, conds := [(10, 30), (9, 30), (2, 30), (10, 28)] }, { number := 537, nolines := 4, conds := [(10, 30), (9, 30), (2, 30), (9, 24)] }, { number := 535, nolines := 4, conds := [(10, 30), (9, 30), (2, 30), (7, 24)] }, { number := 533, nolines := 4, conds := [(10, 30), (9, 30), (2, 30), (2, 24)] }, { number := 530, nolines := 3, conds := [(10, 30), (9, 30), (5, 30)] }, { number := 528, nolines := 3, conds := [(10, 30), (9, 30), (4, 30)] }, { number := 406, nolines := 3, conds := [(10, 30), (9, 30), (3, 30)] }, { number := 404, nolines := 3, conds := [(10, 30), (9, 30), (6, 30)] }, { number := 234, nolines := 3, conds := [(10, 30), (9, 30), (1, 30)] }, { number := 232, nolines := 3, conds := [(10, 30), (9, 30), (8, 30)] }] (hintStreamAt hints_10 7536) =
      (true, 551, hintStreamAt hints_10 7683) := by kernel_rfl

theorem cbp_10_32 :
    evalCBPrefix 10 2 (childCBState cb_10_284) (hintStreamAt hints_10 7731) =
      (true, hintStreamAt hints_10 7842) := by kernel_rfl

theorem cbp_10_33 :
    evalCBState 10 (advanceCBState 2 (childCBState cb_10_284)) (hintStreamAt hints_10 7842) =
      (true, hintStreamAt hints_10 7911) := by kernel_rfl

theorem cbp_10_35 :
    evalCBState 10 (advanceCBState 1 cb_10_284) (hintStreamAt hints_10 7911) =
      (true, hintStreamAt hints_10 8009) := by kernel_rfl

theorem p_10_286 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_286 4105629843349963576032097773515384148851924615144855894615469360273363808232416316502395068480 578 4 67649994 410642334 [{ number := 576, nolines := 5, conds := [(10, 30), (7, 30), (4, 30), (2, 30), (2, 28)] }, { number := 573, nolines := 4, conds := [(10, 30), (7, 30), (4, 30), (5, 30)] }, { number := 571, nolines := 4, conds := [(10, 30), (7, 30), (4, 30), (3, 30)] }, { number := 568, nolines := 3, conds := [(10, 30), (7, 30), (8, 30)] }, { number := 566, nolines := 3, conds := [(10, 30), (7, 30), (6, 30)] }, { number := 563, nolines := 2, conds := [(10, 30), (1, 30)] }, { number := 561, nolines := 2, conds := [(10, 30), (9, 30)] }] (hintStreamAt hints_10 8023) =
      (true, 593, hintStreamAt hints_10 8162) := by kernel_rfl

theorem p_10_291 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_291 4105629843349963576032097773515384148851924615144855894615469360273363808204746077246528426048 600 4 1851850 911262 [{ number := 599, nolines := 4, conds := [(10, 30), (7, 30), (4, 30), (10, 24)] }, { number := 597, nolines := 4, conds := [(10, 30), (7, 30), (4, 30), (7, 24)] }, { number := 595, nolines := 4, conds := [(10, 30), (7, 30), (4, 30), (4, 24)] }, { number := 593, nolines := 4, conds := [(10, 30), (7, 30), (4, 30), (2, 30)] }, { number := 573, nolines := 4, conds := [(10, 30), (7, 30), (4, 30), (5, 30)] }, { number := 571, nolines := 4, conds := [(10, 30), (7, 30), (4, 30), (3, 30)] }, { number := 568, nolines := 3, conds := [(10, 30), (7, 30), (8, 30)] }, { number := 566, nolines := 3, conds := [(10, 30), (7, 30), (6, 30)] }, { number := 563, nolines := 2, conds := [(10, 30), (1, 30)] }, { number := 561, nolines := 2, conds := [(10, 30), (9, 30)] }] (hintStreamAt hints_10 8222) =
      (true, 609, hintStreamAt hints_10 8284) := by kernel_rfl

theorem p_10_293 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_293 4105629843349963576032097773515384148851924615144855894615469360272783523811331064038762483776 610 4 3686858 386974 [{ number := 609, nolines := 4, conds := [(10, 30), (7, 30), (4, 30), (7, 3)] }, { number := 599, nolines := 4, conds := [(10, 30), (7, 30), (4, 30), (10, 24)] }, { number := 597, nolines := 4, conds := [(10, 30), (7, 30), (4, 30), (7, 24)] }, { number := 595, nolines := 4, conds := [(10, 30), (7, 30), (4, 30), (4, 24)] }, { number := 593, nolines := 4, conds := [(10, 30), (7, 30), (4, 30), (2, 30)] }, { number := 573, nolines := 4, conds := [(10, 30), (7, 30), (4, 30), (5, 30)] }, { number := 571, nolines := 4, conds := [(10, 30), (7, 30), (4, 30), (3, 30)] }, { number := 568, nolines := 3, conds := [(10, 30), (7, 30), (8, 30)] }, { number := 566, nolines := 3, conds := [(10, 30), (7, 30), (6, 30)] }, { number := 563, nolines := 2, conds := [(10, 30), (1, 30)] }, { number := 561, nolines := 2, conds := [(10, 30), (9, 30)] }] (hintStreamAt hints_10 8284) =
      (true, 611, hintStreamAt hints_10 8388) := by kernel_rfl

theorem p_10_294 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_294 4105629843349963576032097773515384148851924615144855894615469360273344465391632251975826149440 611 3 3686858 386974 [{ number := 609, nolines := 4, conds := [(10, 30), (7, 30), (4, 30), (7, 3)] }, { number := 599, nolines := 4, conds := [(10, 30), (7, 30), (4, 30), (10, 24)] }, { number := 597, nolines := 4, conds := [(10, 30), (7, 30), (4, 30), (7, 24)] }, { number := 595, nolines := 4, conds := [(10, 30), (7, 30), (4, 30), (4, 24)] }, { number := 593, nolines := 4, conds := [(10, 30), (7, 30), (4, 30), (2, 30)] }, { number := 573, nolines := 4, conds := [(10, 30), (7, 30), (4, 30), (5, 30)] }, { number := 571, nolines := 4, conds := [(10, 30), (7, 30), (4, 30), (3, 30)] }, { number := 568, nolines := 3, conds := [(10, 30), (7, 30), (8, 30)] }, { number := 566, nolines := 3, conds := [(10, 30), (7, 30), (6, 30)] }, { number := 563, nolines := 2, conds := [(10, 30), (1, 30)] }, { number := 561, nolines := 2, conds := [(10, 30), (9, 30)] }] (hintStreamAt hints_10 8388) =
      (true, 622, hintStreamAt hints_10 8480) := by kernel_rfl

theorem p_10_298 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_298 4105629843349963576032097773515384148851924615144855894615469360273363808232416316534523527232 626 4 532938 6416286 [{ number := 624, nolines := 3, conds := [(10, 30), (7, 30), (3, 30)] }, { number := 622, nolines := 3, conds := [(10, 30), (7, 30), (4, 30)] }, { number := 568, nolines := 3, conds := [(10, 30), (7, 30), (8, 30)] }, { number := 566, nolines := 3, conds := [(10, 30), (7, 30), (6, 30)] }, { number := 563, nolines := 2, conds := [(10, 30), (1, 30)] }, { number := 561, nolines := 2, conds := [(10, 30), (9, 30)] }] (hintStreamAt hints_10 8480) =
      (true, 627, hintStreamAt hints_10 8516) := by kernel_rfl

theorem p_10_307 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_307 4105629843349963576032097773515384148851924615144855894615469360273363808232416316533449711680 628 4 1319370 7989150 [{ number := 627, nolines := 4, conds := [(10, 30), (7, 30), (2, 30), (2, 24)] }, { number := 624, nolines := 3, conds := [(10, 30), (7, 30), (3, 30)] }, { number := 622, nolines := 3, conds := [(10, 30), (7, 30), (4, 30)] }, { number := 568, nolines := 3, conds := [(10, 30), (7, 30), (8, 30)] }, { number := 566, nolines := 3, conds := [(10, 30), (7, 30), (6, 30)] }, { number := 563, nolines := 2, conds := [(10, 30), (1, 30)] }, { number := 561, nolines := 2, conds := [(10, 30), (9, 30)] }] (hintStreamAt hints_10 8522) =
      (true, 629, hintStreamAt hints_10 8647) := by kernel_rfl

theorem p_10_308 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_308 4105629843349963576032097773515384148851924615144855894615469360273363808232416316533449711680 628 4 1319370 7989150 [{ number := 627, nolines := 4, conds := [(10, 30), (7, 30), (2, 30), (2, 24)] }, { number := 624, nolines := 3, conds := [(10, 30), (7, 30), (3, 30)] }, { number := 622, nolines := 3, conds := [(10, 30), (7, 30), (4, 30)] }, { number := 568, nolines := 3, conds := [(10, 30), (7, 30), (8, 30)] }, { number := 566, nolines := 3, conds := [(10, 30), (7, 30), (6, 30)] }, { number := 563, nolines := 2, conds := [(10, 30), (1, 30)] }, { number := 561, nolines := 2, conds := [(10, 30), (9, 30)] }] (hintStreamAt hints_10 8647) =
      (true, 629, hintStreamAt hints_10 8775) := by kernel_rfl

theorem p_10_312 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_312 4105629843349963576032097773515384148851924615144855894615469360273363808232416316502311198784 629 3 1319370 7989150 [{ number := 627, nolines := 4, conds := [(10, 30), (7, 30), (2, 30), (2, 24)] }, { number := 624, nolines := 3, conds := [(10, 30), (7, 30), (3, 30)] }, { number := 622, nolines := 3, conds := [(10, 30), (7, 30), (4, 30)] }, { number := 568, nolines := 3, conds := [(10, 30), (7, 30), (8, 30)] }, { number := 566, nolines := 3, conds := [(10, 30), (7, 30), (6, 30)] }, { number := 563, nolines := 2, conds := [(10, 30), (1, 30)] }, { number := 561, nolines := 2, conds := [(10, 30), (9, 30)] }] (hintStreamAt hints_10 8778) =
      (true, 630, hintStreamAt hints_10 8928) := by kernel_rfl

theorem p_10_318 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_318 4105629843349963576032097773515384148851924615144855894615469360273363808232424635270334611520 656 4 532746 6416286 [{ number := 653, nolines := 2, conds := [(10, 30), (5, 30)] }, { number := 639, nolines := 2, conds := [(10, 30), (3, 30)] }, { number := 637, nolines := 2, conds := [(10, 30), (7, 30)] }, { number := 563, nolines := 2, conds := [(10, 30), (1, 30)] }, { number := 561, nolines := 2, conds := [(10, 30), (9, 30)] }] (hintStreamAt hints_10 9000) =
      (true, 657, hintStreamAt hints_10 9092) := by kernel_rfl

theorem p_10_320 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_320 4105629843349963576032097773515384148851924615144855894615469360273363808232424635270233874496 658 4 1057034 6416286 [{ number := 657, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (2, 24)] }, { number := 653, nolines := 2, conds := [(10, 30), (5, 30)] }, { number := 639, nolines := 2, conds := [(10, 30), (3, 30)] }, { number := 637, nolines := 2, conds := [(10, 30), (7, 30)] }, { number := 563, nolines := 2, conds := [(10, 30), (1, 30)] }, { number := 561, nolines := 2, conds := [(10, 30), (9, 30)] }] (hintStreamAt hints_10 9092) =
      (true, 659, hintStreamAt hints_10 9189) := by kernel_rfl

theorem p_10_324 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_324 4105629843349963576032097773515384148851924615144855894615469360273363808225500349193582305344 664 4 2629898 6416286 [{ number := 663, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (8, 24)] }, { number := 661, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (6, 24)] }, { number := 659, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (4, 24)] }, { number := 657, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (2, 24)] }, { number := 653, nolines := 2, conds := [(10, 30), (5, 30)] }, { number := 639, nolines := 2, conds := [(10, 30), (3, 30)] }, { number := 637, nolines := 2, conds := [(10, 30), (7, 30)] }, { number := 563, nolines := 2, conds := [(10, 30), (1, 30)] }, { number := 561, nolines := 2, conds := [(10, 30), (9, 30)] }] (hintStreamAt hints_10 9228) =
      (true, 665, hintStreamAt hints_10 9323) := by kernel_rfl

theorem p_10_327 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_327 4105629843349963576032097773515384148851924615144855894615469360273363505973292858453365375040 667 5 36970762 477751198 [{ number := 665, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (10, 24)] }, { number := 663, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (8, 24)] }, { number := 661, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (6, 24)] }, { number := 659, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (4, 24)] }, { number := 657, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (2, 24)] }, { number := 653, nolines := 2, conds := [(10, 30), (5, 30)] }, { number := 639, nolines := 2, conds := [(10, 30), (3, 30)] }, { number := 637, nolines := 2, conds := [(10, 30), (7, 30)] }, { number := 563, nolines := 2, conds := [(10, 30), (1, 30)] }, { number := 561, nolines := 2, conds := [(10, 30), (9, 30)] }] (hintStreamAt hints_10 9323) =
      (true, 668, hintStreamAt hints_10 9412) := by kernel_rfl

theorem p_10_329 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_329 4105629843349963576032097773515384148851924615144855894615469360273363505973292858247206936640 669 5 104079626 477751198 [{ number := 668, nolines := 5, conds := [(10, 30), (4, 30), (2, 30), (13, 30), (2, 28)] }, { number := 665, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (10, 24)] }, { number := 663, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (8, 24)] }, { number := 661, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (6, 24)] }, { number := 659, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (4, 24)] }, { number := 657, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (2, 24)] }, { number := 653, nolines := 2, conds := [(10, 30), (5, 30)] }, { number := 639, nolines := 2, conds := [(10, 30), (3, 30)] }, { number := 637, nolines := 2, conds := [(10, 30), (7, 30)] }, { number := 563, nolines := 2, conds := [(10, 30), (1, 30)] }, { number := 561, nolines := 2, conds := [(10, 30), (9, 30)] }] (hintStreamAt hints_10 9412) =
      (true, 688, hintStreamAt hints_10 9494) := by kernel_rfl

theorem p_10_331 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_331 4105629843349963576032097773515384148851924615144855894615469360273363505973292858178453905472 689 5 70525194 477751198 [{ number := 688, nolines := 5, conds := [(10, 30), (4, 30), (2, 30), (13, 30), (6, 28)] }, { number := 668, nolines := 5, conds := [(10, 30), (4, 30), (2, 30), (13, 30), (2, 28)] }, { number := 665, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (10, 24)] }, { number := 663, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (8, 24)] }, { number := 661, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (6, 24)] }, { number := 659, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (4, 24)] }, { number := 657, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (2, 24)] }, { number := 653, nolines := 2, conds := [(10, 30), (5, 30)] }, { number := 639, nolines := 2, conds := [(10, 30), (3, 30)] }, { number := 637, nolines := 2, conds := [(10, 30), (7, 30)] }, { number := 563, nolines := 2, conds := [(10, 30), (1, 30)] }, { number := 561, nolines := 2, conds := [(10, 30), (9, 30)] }] (hintStreamAt hints_10 9494) =
      (true, 690, hintStreamAt hints_10 9592) := by kernel_rfl

theorem p_10_335 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_335 4105629843349963576032097773515384148851924615144855889170951489538347946822269316925302775872 696 4 204742922 511305630 [{ number := 692, nolines := 5, conds := [(10, 30), (4, 30), (2, 30), (13, 30), (11, 28)] }, { number := 690, nolines := 5, conds := [(10, 30), (4, 30), (2, 30), (13, 30), (4, 28)] }, { number := 688, nolines := 5, conds := [(10, 30), (4, 30), (2, 30), (13, 30), (6, 28)] }, { number := 668, nolines := 5, conds := [(10, 30), (4, 30), (2, 30), (13, 30), (2, 28)] }, { number := 665, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (10, 24)] }, { number := 663, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (8, 24)] }, { number := 661, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (6, 24)] }, { number := 659, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (4, 24)] }, { number := 657, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (2, 24)] }, { number := 653, nolines := 2, conds := [(10, 30), (5, 30)] }, { number := 639, nolines := 2, conds := [(10, 30), (3, 30)] }, { number := 637, nolines := 2, conds := [(10, 30), (7, 30)] }, { number := 563, nolines := 2, conds := [(10, 30), (1, 30)] }, { number := 561, nolines := 2, conds := [(10, 30), (9, 30)] }] (hintStreamAt hints_10 9631) =
      (true, 733, hintStreamAt hints_10 9779) := by kernel_rfl

theorem p_10_339 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_339 4105629843349963576032097773515384148851924615144855894575592520399807265073986440171121557568 737 5 35135754 470149022 [{ number := 735, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (20, 30)] }, { number := 733, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (13, 30)] }, { number := 665, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (10, 24)] }, { number := 663, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (8, 24)] }, { number := 661, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (6, 24)] }, { number := 659, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (4, 24)] }, { number := 657, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (2, 24)] }, { number := 653, nolines := 2, conds := [(10, 30), (5, 30)] }, { number := 639, nolines := 2, conds := [(10, 30), (3, 30)] }, { number := 637, nolines := 2, conds := [(10, 30), (7, 30)] }, { number := 563, nolines := 2, conds := [(10, 30), (1, 30)] }, { number := 561, nolines := 2, conds := [(10, 30), (9, 30)] }] (hintStreamAt hints_10 9779) =
      (true, 738, hintStreamAt hints_10 9897) := by kernel_rfl

theorem p_10_340 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_340 4105629843349963576032097773515384148851924615144855894575592520399807265073986440171121549376 738 4 35135754 470149022 [{ number := 735, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (20, 30)] }, { number := 733, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (13, 30)] }, { number := 665, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (10, 24)] }, { number := 663, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (8, 24)] }, { number := 661, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (6, 24)] }, { number := 659, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (4, 24)] }, { number := 657, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (2, 24)] }, { number := 653, nolines := 2, conds := [(10, 30), (5, 30)] }, { number := 639, nolines := 2, conds := [(10, 30), (3, 30)] }, { number := 637, nolines := 2, conds := [(10, 30), (7, 30)] }, { number := 563, nolines := 2, conds := [(10, 30), (1, 30)] }, { number := 561, nolines := 2, conds := [(10, 30), (9, 30)] }] (hintStreamAt hints_10 9897) =
      (true, 749, hintStreamAt hints_10 9963) := by kernel_rfl

theorem p_10_341 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_341 4105629843349963576032097773515384148851924615144855894575592520399807265073986440514718949440 749 3 1581322 386974 [{ number := 735, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (20, 30)] }, { number := 733, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (13, 30)] }, { number := 665, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (10, 24)] }, { number := 663, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (8, 24)] }, { number := 661, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (6, 24)] }, { number := 659, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (4, 24)] }, { number := 657, nolines := 4, conds := [(10, 30), (4, 30), (2, 30), (2, 24)] }, { number := 653, nolines := 2, conds := [(10, 30), (5, 30)] }, { number := 639, nolines := 2, conds := [(10, 30), (3, 30)] }, { number := 637, nolines := 2, conds := [(10, 30), (7, 30)] }, { number := 563, nolines := 2, conds := [(10, 30), (1, 30)] }, { number := 561, nolines := 2, conds := [(10, 30), (9, 30)] }] (hintStreamAt hints_10 9963) =
      (true, 798, hintStreamAt hints_10 9978) := by kernel_rfl

theorem cbp_10_37 :
    evalCBPrefix 10 1 (childCBState cb_10_353) (hintStreamAt hints_10 9985) =
      (true, hintStreamAt hints_10 10077) := by kernel_rfl

theorem cbp_10_38 :
    evalCBState 10 (advanceCBState 1 (childCBState cb_10_353)) (hintStreamAt hints_10 10077) =
      (true, hintStreamAt hints_10 10222) := by kernel_rfl

theorem cbp_10_40 :
    evalCBState 10 (advanceCBState 1 cb_10_353) (hintStreamAt hints_10 10222) =
      (true, hintStreamAt hints_10 10362) := by kernel_rfl

theorem cbp_10_42 :
    evalCBPrefix 10 7 cb_10_363 (hintStreamAt hints_10 10408) =
      (true, hintStreamAt hints_10 10506) := by kernel_rfl

theorem cbp_10_43 :
    evalCBState 10 (advanceCBState 7 cb_10_363) (hintStreamAt hints_10 10506) =
      (true, hintStreamAt hints_10 10601) := by kernel_rfl

theorem p_10_364 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_364 4105629843349963576032097773515384148851924615144855894615469360273363666533751587102722887744 808 4 3170570 386974 [{ number := 807, nolines := 4, conds := [(10, 30), (4, 30), (6, 30), (10, 24)] }, { number := 805, nolines := 4, conds := [(10, 30), (4, 30), (6, 30), (6, 24)] }, { number := 803, nolines := 4, conds := [(10, 30), (4, 30), (6, 30), (4, 24)] }, { number := 801, nolines := 4, conds := [(10, 30), (4, 30), (6, 30), (8, 30)] }, { number := 798, nolines := 3, conds := [(10, 30), (4, 30), (2, 30)] }, { number := 653, nolines := 2, conds := [(10, 30), (5, 30)] }, { number := 639, nolines := 2, conds := [(10, 30), (3, 30)] }, { number := 637, nolines := 2, conds := [(10, 30), (7, 30)] }, { number := 563, nolines := 2, conds := [(10, 30), (1, 30)] }, { number := 561, nolines := 2, conds := [(10, 30), (9, 30)] }] (hintStreamAt hints_10 10601) =
      (true, 809, hintStreamAt hints_10 10664) := by kernel_rfl

theorem p_10_365 :
    verifyTreePureRec 10 shiftedOutsTable_10 n_10_365 4105629843349963576032097773515384148851924615144855894615469360273363803482379590322434084928 809 3 3170570 386974 [{ number := 807, nolines := 4, conds := [(10, 30), (4, 30), (6, 30), (10, 24)] }, { number := 805, nolines := 4, conds := [(10, 30), (4, 30), (6, 30), (6, 24)] }, { number := 803, nolines := 4, conds := [(10, 30), (4, 30), (6, 30), (4, 24)] }, { number := 801, nolines := 4, conds := [(10, 30), (4, 30), (6, 30), (8, 30)] }, { number := 798, nolines := 3, conds := [(10, 30), (4, 30), (2, 30)] }, { number := 653, nolines := 2, conds := [(10, 30), (5, 30)] }, { number := 639, nolines := 2, conds := [(10, 30), (3, 30)] }, { number := 637, nolines := 2, conds := [(10, 30), (7, 30)] }, { number := 563, nolines := 2, conds := [(10, 30), (1, 30)] }, { number := 561, nolines := 2, conds := [(10, 30), (9, 30)] }] (hintStreamAt hints_10 10664) =
      (true, 834, hintStreamAt hints_10 10745) := by kernel_rfl

end Math.Discharging
