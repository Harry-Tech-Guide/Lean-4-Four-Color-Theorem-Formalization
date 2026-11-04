import FourColorTheorem.Math.TestDischarging
import FourColorTheorem.Math.U633Parser
import FourColorTheorem.Math.DischargingSplit
import FourColorTheorem.Math.Batch.DischargeDeg7_Defs

set_option maxHeartbeats 0

namespace Math.Discharging

theorem p_7_294 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_294 3316501375720912038232847094038129170169629371110383356009624387648 1245 5 8708968641 1550848065 [{ number := 1243, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (7, 28), (14, 1)] }, { number := 1241, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (7, 28), (12, 1)] }, { number := 1231, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (7, 28), (7, 24)] }, { number := 1229, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (7, 28), (6, 24)] }, { number := 1207, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (7, 28), (4, 24)] }, { number := 1205, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (7, 28), (2, 24)] }, { number := 1063, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (7, 28), (4, 3)] }, { number := 1061, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (7, 28), (2, 3)] }, { number := 971, nolines := 4, conds := [(1, 1), (3, 1), (5, 1), (6, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 10162) =
      (true, 1262, hintStreamAt hints_7 10230) := by kernel_rfl

theorem p_7_298 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_298 3316501375720912038232847094038129170169648718645863947274182557760 1266 6 4330115265 3631222849 [{ number := 1265, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 24), (4, 16)] }, { number := 1262, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (7, 28)] }, { number := 971, nolines := 4, conds := [(1, 1), (3, 1), (5, 1), (6, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 10249) =
      (true, 1271, hintStreamAt hints_7 10288) := by kernel_rfl

theorem cbp_7_15 :
    evalCBPrefix 7 2 cb_7_305 (hintStreamAt hints_7 10296) =
      (true, hintStreamAt hints_7 10410) := by kernel_rfl

theorem cbp_7_16 :
    evalCBPrefix 7 11 (advanceCBState 2 cb_7_305) (hintStreamAt hints_7 10410) =
      (true, hintStreamAt hints_7 10560) := by kernel_rfl

theorem cbp_7_17 :
    evalCBState 7 (advanceCBState 11 (advanceCBState 2 cb_7_305)) (hintStreamAt hints_7 10560) =
      (true, hintStreamAt hints_7 10602) := by kernel_rfl

theorem p_7_307 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_307 3316501375720912038232847094038129170169629375832750113207487922240 1274 6 4330115265 26179801153 [{ number := 1273, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 24), (14, 1)] }, { number := 1271, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 24), (4, 3)] }, { number := 1265, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 24), (4, 16)] }, { number := 1262, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (7, 28)] }, { number := 971, nolines := 4, conds := [(1, 1), (3, 1), (5, 1), (6, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 10602) =
      (true, 1275, hintStreamAt hints_7 10691) := by kernel_rfl

theorem p_7_309 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_309 3316501375720912038232847094038129170169629375832750112932542906432 1276 6 6477598913 26179801153 [{ number := 1275, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 24), (4, 24)] }, { number := 1273, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 24), (14, 1)] }, { number := 1271, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 24), (4, 3)] }, { number := 1265, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 24), (4, 16)] }, { number := 1262, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (7, 28)] }, { number := 971, nolines := 4, conds := [(1, 1), (3, 1), (5, 1), (6, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 10691) =
      (true, 1277, hintStreamAt hints_7 10751) := by kernel_rfl

theorem p_7_312 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_312 3316501375720912038232847094038129170169629073601294926425882984512 1280 6 8625082561 32622252097 [{ number := 1279, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 24), (13, 1)] }, { number := 1277, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 24), (6, 24)] }, { number := 1275, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 24), (4, 24)] }, { number := 1273, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 24), (14, 1)] }, { number := 1271, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 24), (4, 3)] }, { number := 1265, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 24), (4, 16)] }, { number := 1262, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (7, 28)] }, { number := 971, nolines := 4, conds := [(1, 1), (3, 1), (5, 1), (6, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 10752) =
      (true, 1281, hintStreamAt hints_7 10829) := by kernel_rfl

theorem p_7_313 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_313 3316501375720912038232847094038129170169629073601286763651558375488 1281 5 8625082561 32622252097 [{ number := 1279, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 24), (13, 1)] }, { number := 1277, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 24), (6, 24)] }, { number := 1275, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 24), (4, 24)] }, { number := 1273, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 24), (14, 1)] }, { number := 1271, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 24), (4, 3)] }, { number := 1265, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 24), (4, 16)] }, { number := 1262, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (7, 28)] }, { number := 971, nolines := 4, conds := [(1, 1), (3, 1), (5, 1), (6, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 10829) =
      (true, 1290, hintStreamAt hints_7 10955) := by kernel_rfl

theorem cbp_7_20 :
    evalCBPrefix 7 8 cb_7_325 (hintStreamAt hints_7 10962) =
      (true, hintStreamAt hints_7 11100) := by kernel_rfl

theorem cbp_7_21 :
    evalCBState 7 (advanceCBState 8 cb_7_325) (hintStreamAt hints_7 11100) =
      (true, hintStreamAt hints_7 11139) := by kernel_rfl

theorem p_7_327 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_327 3316501375720912038232847094038129170169629375832750113207387185216 1303 5 68702401 57675841 [{ number := 1302, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (14, 1)] }, { number := 1290, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 24)] }, { number := 1262, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (7, 28)] }, { number := 971, nolines := 4, conds := [(1, 1), (3, 1), (5, 1), (6, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 11139) =
      (true, 1316, hintStreamAt hints_7 11167) := by kernel_rfl

theorem cbp_7_23 :
    evalCBPrefix 7 1 cb_7_335 (hintStreamAt hints_7 11168) =
      (true, hintStreamAt hints_7 11262) := by kernel_rfl

theorem cbp_7_24 :
    evalCBState 7 (advanceCBState 1 cb_7_335) (hintStreamAt hints_7 11262) =
      (true, hintStreamAt hints_7 11398) := by kernel_rfl

theorem cbp_7_26 :
    evalCBPrefix 7 4 (childCBState cb_7_342) (hintStreamAt hints_7 11399) =
      (true, hintStreamAt hints_7 11545) := by kernel_rfl

theorem cbp_7_27 :
    evalCBState 7 (advanceCBState 4 (childCBState cb_7_342)) (hintStreamAt hints_7 11545) =
      (true, hintStreamAt hints_7 11563) := by kernel_rfl

theorem cbp_7_29 :
    evalCBState 7 (advanceCBState 1 cb_7_342) (hintStreamAt hints_7 11563) =
      (true, hintStreamAt hints_7 11690) := by kernel_rfl

theorem p_7_350 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_350 3316501375720912038232847094038129170169629073601286763651692511296 1324 6 8625082561 1550848065 [{ number := 1323, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 28), (13, 1)] }, { number := 1321, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 28), (6, 24)] }, { number := 1319, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 28), (4, 16)] }, { number := 1316, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (4, 3)] }, { number := 1302, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (14, 1)] }, { number := 1290, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 24)] }, { number := 1262, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (7, 28)] }, { number := 971, nolines := 4, conds := [(1, 1), (3, 1), (5, 1), (6, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 11692) =
      (true, 1325, hintStreamAt hints_7 11823) := by kernel_rfl

theorem p_7_351 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_351 3316501375720912038232847094038129170169629073601286763651692511296 1324 6 8625082561 1550848065 [{ number := 1323, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 28), (13, 1)] }, { number := 1321, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 28), (6, 24)] }, { number := 1319, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 28), (4, 16)] }, { number := 1316, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (4, 3)] }, { number := 1302, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (14, 1)] }, { number := 1290, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 24)] }, { number := 1262, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (7, 28)] }, { number := 971, nolines := 4, conds := [(1, 1), (3, 1), (5, 1), (6, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 11823) =
      (true, 1325, hintStreamAt hints_7 11923) := by kernel_rfl

theorem p_7_355 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_355 3316501375720912038232847094038129170169629073600772508869107925056 1330 6 9698824385 3698331713 [{ number := 1329, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 28), (9, 1)] }, { number := 1327, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 28), (4, 24)] }, { number := 1325, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 28), (8, 1)] }, { number := 1323, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 28), (13, 1)] }, { number := 1321, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 28), (6, 24)] }, { number := 1319, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 28), (4, 16)] }, { number := 1316, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (4, 3)] }, { number := 1302, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (14, 1)] }, { number := 1290, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 24)] }, { number := 1262, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (7, 28)] }, { number := 971, nolines := 4, conds := [(1, 1), (3, 1), (5, 1), (6, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 12009) =
      (true, 1331, hintStreamAt hints_7 12089) := by kernel_rfl

theorem p_7_356 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_356 3316501375720912038232847094038129170169629073601240883230354456640 1331 5 9698824385 3698331713 [{ number := 1329, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 28), (9, 1)] }, { number := 1327, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 28), (4, 24)] }, { number := 1325, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 28), (8, 1)] }, { number := 1323, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 28), (13, 1)] }, { number := 1321, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 28), (6, 24)] }, { number := 1319, nolines := 6, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 28), (4, 16)] }, { number := 1316, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (4, 3)] }, { number := 1302, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (14, 1)] }, { number := 1290, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 24)] }, { number := 1262, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (7, 28)] }, { number := 971, nolines := 4, conds := [(1, 1), (3, 1), (5, 1), (6, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 12089) =
      (true, 1336, hintStreamAt hints_7 12213) := by kernel_rfl

theorem p_7_357 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_357 3316501375720912038232847094038129170169629375832750113207823376448 1336 4 35147969 477106241 [{ number := 1316, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (4, 3)] }, { number := 1302, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (14, 1)] }, { number := 1290, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (2, 24)] }, { number := 1262, nolines := 5, conds := [(1, 1), (3, 1), (5, 1), (6, 28), (7, 28)] }, { number := 971, nolines := 4, conds := [(1, 1), (3, 1), (5, 1), (6, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 12213) =
      (true, 1347, hintStreamAt hints_7 12337) := by kernel_rfl

theorem cbp_7_31 :
    evalCBPrefix 7 8 cb_7_369 (hintStreamAt hints_7 12348) =
      (true, hintStreamAt hints_7 12478) := by kernel_rfl

theorem cbp_7_32 :
    evalCBState 7 (advanceCBState 8 cb_7_369) (hintStreamAt hints_7 12478) =
      (true, hintStreamAt hints_7 12551) := by kernel_rfl

theorem p_7_376 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_376 3316501375720912038232847094038129170169648718645863761625731047488 1368 6 7651467457 26280472641 [{ number := 1367, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (6, 16)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 12582) =
      (true, 1369, hintStreamAt hints_7 12662) := by kernel_rfl

theorem p_7_382 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_382 3316501375720912038232847094038129167792803843217933554654575337536 1370 6 17315143873 1584410689 [{ number := 1369, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (7, 24)] }, { number := 1367, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (6, 16)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 12668) =
      (true, 1371, hintStreamAt hints_7 12744) := by kernel_rfl

theorem p_7_383 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_383 3316501375720912038232847094038129167792803843217933554654575337536 1370 6 17315143873 1584410689 [{ number := 1369, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (7, 24)] }, { number := 1367, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (6, 16)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 12744) =
      (true, 1371, hintStreamAt hints_7 12863) := by kernel_rfl

theorem p_7_385 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_385 3316501375720912038232847094038129170090411489187952235148539600960 1372 6 14093918401 1584410689 [{ number := 1369, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (7, 24)] }, { number := 1367, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (6, 16)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 12863) =
      (true, 1385, hintStreamAt hints_7 12952) := by kernel_rfl

theorem p_7_388 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_388 3316501375720912038232847094038129170089839969506729418656441442368 1388 6 15167660225 1584410689 [{ number := 1387, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (6, 24)] }, { number := 1385, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (13, 1)] }, { number := 1369, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (7, 24)] }, { number := 1367, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (6, 16)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 12983) =
      (true, 1397, hintStreamAt hints_7 13031) := by kernel_rfl

theorem p_7_390 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_390 3316501375720912038232847094038129170090400911087030597797412085824 1398 6 7651467457 30575439937 [{ number := 1397, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (14, 1)] }, { number := 1387, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (6, 24)] }, { number := 1385, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (13, 1)] }, { number := 1369, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (7, 24)] }, { number := 1367, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (6, 16)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 13031) =
      (true, 1399, hintStreamAt hints_7 13096) := by kernel_rfl

theorem p_7_392 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_392 3316501375720912038232847094038129170090400911087030589001251954752 1400 6 4430241985 26280472641 [{ number := 1399, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (7, 28)] }, { number := 1397, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (14, 1)] }, { number := 1387, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (6, 24)] }, { number := 1385, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (13, 1)] }, { number := 1369, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (7, 24)] }, { number := 1367, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (6, 16)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 13096) =
      (true, 1413, hintStreamAt hints_7 13153) := by kernel_rfl

theorem p_7_394 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_394 3316501375720912038232847094038129170090400911086976545805387964480 1414 6 9798951105 30575439937 [{ number := 1413, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (4, 24)] }, { number := 1399, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (7, 28)] }, { number := 1397, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (14, 1)] }, { number := 1387, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (6, 24)] }, { number := 1385, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (13, 1)] }, { number := 1369, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (7, 24)] }, { number := 1367, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (6, 16)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 13153) =
      (true, 1415, hintStreamAt hints_7 13224) := by kernel_rfl

theorem p_7_396 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_396 3316501375720912038232847094038129170090400306623616378528063561792 1416 6 14093918401 30575439937 [{ number := 1415, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (9, 28)] }, { number := 1413, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (4, 24)] }, { number := 1399, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (7, 28)] }, { number := 1397, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (14, 1)] }, { number := 1387, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (6, 24)] }, { number := 1385, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (13, 1)] }, { number := 1369, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (7, 24)] }, { number := 1367, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (6, 16)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 13224) =
      (true, 1417, hintStreamAt hints_7 13307) := by kernel_rfl

theorem p_7_397 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_397 3316501375720912038232847094038129170090392448605788883438427971648 1417 5 14093918401 30575439937 [{ number := 1415, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (9, 28)] }, { number := 1413, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (4, 24)] }, { number := 1399, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (7, 28)] }, { number := 1397, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (14, 1)] }, { number := 1387, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (6, 24)] }, { number := 1385, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (13, 1)] }, { number := 1369, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (7, 24)] }, { number := 1367, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30), (6, 16)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 13307) =
      (true, 1450, hintStreamAt hints_7 13437) := by kernel_rfl

theorem p_7_401 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_401 3316501375720912038232847094038129167872032005732189836124275089472 1454 6 17264812225 3698339905 [{ number := 1450, nolines := 5, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 13438) =
      (true, 1467, hintStreamAt hints_7 13474) := by kernel_rfl

theorem p_7_404 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_404 3316501375720912038232847094038129169931964231103008464807773085760 1472 6 9748619457 30541885505 [{ number := 1471, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (5, 28), (7, 24)] }, { number := 1450, nolines := 5, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 13493) =
      (true, 1483, hintStreamAt hints_7 13527) := by kernel_rfl

theorem p_7_409 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_409 3316501375720912038232847094038129169931906202663216584915025141824 1506 6 6527393985 30541885505 [{ number := 1505, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (5, 28), (7, 28)] }, { number := 1501, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (5, 28), (14, 3)] }, { number := 1493, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (5, 28), (14, 1)] }, { number := 1483, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (5, 28), (9, 28)] }, { number := 1471, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (5, 28), (7, 24)] }, { number := 1450, nolines := 5, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 13585) =
      (true, 1533, hintStreamAt hints_7 13622) := by kernel_rfl

theorem p_7_410 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_410 3316501375720912038232847094038129169931906202663216583128318746688 1533 5 6527393985 30541885505 [{ number := 1505, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (5, 28), (7, 28)] }, { number := 1501, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (5, 28), (14, 3)] }, { number := 1493, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (5, 28), (14, 1)] }, { number := 1483, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (5, 28), (9, 28)] }, { number := 1471, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (5, 28), (7, 24)] }, { number := 1450, nolines := 5, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 13622) =
      (true, 1548, hintStreamAt hints_7 13671) := by kernel_rfl

theorem p_7_415 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_415 3316501375720912038232847094038129169931964226380696119938616926272 1560 6 7617913025 30122455105 [{ number := 1559, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (6, 3), (12, 1)] }, { number := 1548, nolines := 5, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (5, 28)] }, { number := 1450, nolines := 5, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 13715) =
      (true, 1587, hintStreamAt hints_7 13848) := by kernel_rfl

theorem p_7_416 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_416 3316501375720912038232847094038129169931964226380696005589407637568 1587 5 7617913025 30122455105 [{ number := 1559, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (6, 3), (12, 1)] }, { number := 1548, nolines := 5, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (5, 28)] }, { number := 1450, nolines := 5, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 13848) =
      (true, 1598, hintStreamAt hints_7 13882) := by kernel_rfl

theorem p_7_417 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_417 3316501375720912038232847094038129169931964231103062613391061557312 1598 4 101720257 57684033 [{ number := 1548, nolines := 5, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (5, 28)] }, { number := 1450, nolines := 5, conds := [(1, 1), (3, 1), (2, 3), (4, 28), (8, 30)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 13882) =
      (true, 1621, hintStreamAt hints_7 13945) := by kernel_rfl

theorem p_7_425 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_425 3316501375720912038232847094038129170090401213285051052009235685440 1632 6 10839400641 3698339905 [{ number := 1627, nolines := 4, conds := [(1, 1), (3, 1), (2, 3), (14, 1)] }, { number := 1625, nolines := 4, conds := [(1, 1), (3, 1), (2, 3), (10, 1)] }, { number := 1623, nolines := 4, conds := [(1, 1), (3, 1), (2, 3), (7, 28)] }, { number := 1621, nolines := 4, conds := [(1, 1), (3, 1), (2, 3), (4, 28)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 13953) =
      (true, 1653, hintStreamAt hints_7 13984) := by kernel_rfl

theorem p_7_428 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_428 3316501375720912038232847094038129167871973977289397890376192499776 1656 6 17281851585 3698339905 [{ number := 1655, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (5, 28), (6, 28), (14, 3)] }, { number := 1653, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (5, 28), (6, 28), (10, 3)] }, { number := 1627, nolines := 4, conds := [(1, 1), (3, 1), (2, 3), (14, 1)] }, { number := 1625, nolines := 4, conds := [(1, 1), (3, 1), (2, 3), (10, 1)] }, { number := 1623, nolines := 4, conds := [(1, 1), (3, 1), (2, 3), (7, 28)] }, { number := 1621, nolines := 4, conds := [(1, 1), (3, 1), (2, 3), (4, 28)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 13984) =
      (true, 1675, hintStreamAt hints_7 14023) := by kernel_rfl

theorem p_7_429 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_429 3316501375720912038232847094038129169931906202660270667808335208512 1675 5 17281851585 3698339905 [{ number := 1655, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (5, 28), (6, 28), (14, 3)] }, { number := 1653, nolines := 6, conds := [(1, 1), (3, 1), (2, 3), (5, 28), (6, 28), (10, 3)] }, { number := 1627, nolines := 4, conds := [(1, 1), (3, 1), (2, 3), (14, 1)] }, { number := 1625, nolines := 4, conds := [(1, 1), (3, 1), (2, 3), (10, 1)] }, { number := 1623, nolines := 4, conds := [(1, 1), (3, 1), (2, 3), (7, 28)] }, { number := 1621, nolines := 4, conds := [(1, 1), (3, 1), (2, 3), (4, 28)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 14023) =
      (true, 1708, hintStreamAt hints_7 14056) := by kernel_rfl

theorem p_7_430 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_430 3316501375720912038232847094038129170169629375831597189945064955968 1708 4 101982401 477114433 [{ number := 1627, nolines := 4, conds := [(1, 1), (3, 1), (2, 3), (14, 1)] }, { number := 1625, nolines := 4, conds := [(1, 1), (3, 1), (2, 3), (10, 1)] }, { number := 1623, nolines := 4, conds := [(1, 1), (3, 1), (2, 3), (7, 28)] }, { number := 1621, nolines := 4, conds := [(1, 1), (3, 1), (2, 3), (4, 28)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 14056) =
      (true, 1727, hintStreamAt hints_7 14085) := by kernel_rfl

theorem p_7_435 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_435 3316501375720912038232847094038129170169648718645864044060633055296 1734 6 7617925313 26247020609 [{ number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 14086) =
      (true, 1735, hintStreamAt hints_7 14141) := by kernel_rfl

theorem p_7_439 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_439 3316501375720912038232847094038129170169648718645863956099635658816 1739 7 282495832257 1679809429569 [{ number := 1738, nolines := 7, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (7, 28), (2, 16)] }, { number := 1735, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (7, 24)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 14141) =
      (true, 1740, hintStreamAt hints_7 14196) := by kernel_rfl

theorem p_7_443 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_443 3316501375720912038232847094038128845650553461419668016944019456064 1745 7 1244568506561 2092126289985 [{ number := 1744, nolines := 7, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (7, 28), (14, 28)] }, { number := 1742, nolines := 7, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (7, 28), (10, 28)] }, { number := 1740, nolines := 7, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (7, 28), (4, 24)] }, { number := 1738, nolines := 7, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (7, 28), (2, 16)] }, { number := 1735, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (7, 24)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 14274) =
      (true, 1758, hintStreamAt hints_7 14404) := by kernel_rfl

theorem p_7_446 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_446 3316501375720912038231419846345413474731439081075141810257270194240 1762 6 351215308993 1679809429569 [{ number := 1744, nolines := 7, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (7, 28), (14, 28)] }, { number := 1742, nolines := 7, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (7, 28), (10, 28)] }, { number := 1740, nolines := 7, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (7, 28), (4, 24)] }, { number := 1738, nolines := 7, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (7, 28), (2, 16)] }, { number := 1735, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (7, 24)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 14442) =
      (true, 1773, hintStreamAt hints_7 14580) := by kernel_rfl

theorem p_7_448 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_448 3316501375720912038232847094038129170169068434252448925299750846528 1774 6 15134118081 1550958657 [{ number := 1773, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (7, 28)] }, { number := 1735, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (7, 24)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 14580) =
      (true, 1775, hintStreamAt hints_7 14728) := by kernel_rfl

theorem p_7_454 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_454 3316501375720912038232847094038129170169079314584825455862408855616 1784 6 15134118081 3698442305 [{ number := 1783, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (13, 28)] }, { number := 1781, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (6, 16)] }, { number := 1779, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (4, 24)] }, { number := 1777, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (2, 16)] }, { number := 1775, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (14, 1)] }, { number := 1773, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (7, 28)] }, { number := 1735, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (7, 24)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 14834) =
      (true, 1797, hintStreamAt hints_7 14981) := by kernel_rfl

theorem p_7_458 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_458 3316501375720911874544663712977002331356880963469805137455894282304 1803 5 29092761793 30541987905 [{ number := 1801, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (10, 28)] }, { number := 1799, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (6, 24)] }, { number := 1797, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (14, 3)] }, { number := 1783, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (13, 28)] }, { number := 1781, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (6, 16)] }, { number := 1779, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (4, 24)] }, { number := 1777, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (2, 16)] }, { number := 1775, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (14, 1)] }, { number := 1773, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (7, 28)] }, { number := 1735, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28), (7, 24)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 15083) =
      (true, 1822, hintStreamAt hints_7 15216) := by kernel_rfl

theorem p_7_461 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_461 3316501375720912038232847094038129170169648718645864059866112655424 1824 6 2265993409 17657086017 [{ number := 1822, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 15216) =
      (true, 1825, hintStreamAt hints_7 15264) := by kernel_rfl

theorem cbp_7_34 :
    evalCBPrefix 7 2 cb_7_469 (hintStreamAt hints_7 15264) =
      (true, hintStreamAt hints_7 15385) := by kernel_rfl

theorem cbp_7_35 :
    evalCBState 7 (advanceCBState 2 cb_7_469) (hintStreamAt hints_7 15385) =
      (true, hintStreamAt hints_7 15531) := by kernel_rfl

theorem cbp_7_37 :
    evalCBPrefix 7 2 cb_7_476 (hintStreamAt hints_7 15531) =
      (true, hintStreamAt hints_7 15652) := by kernel_rfl

theorem cbp_7_38 :
    evalCBState 7 (advanceCBState 2 cb_7_476) (hintStreamAt hints_7 15652) =
      (true, hintStreamAt hints_7 15798) := by kernel_rfl

theorem cbp_7_40 :
    evalCBPrefix 7 3 cb_7_482 (hintStreamAt hints_7 15798) =
      (true, hintStreamAt hints_7 15942) := by kernel_rfl

theorem cbp_7_41 :
    evalCBState 7 (advanceCBState 3 cb_7_482) (hintStreamAt hints_7 15942) =
      (true, hintStreamAt hints_7 15995) := by kernel_rfl

theorem p_7_484 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_484 3316501375720912038232847094038129170169639651669935147992138154048 1833 7 151516106945 1650818400321 [{ number := 1832, nolines := 7, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28), (13, 1), (10, 28)] }, { number := 1830, nolines := 7, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28), (13, 1), (5, 24)] }, { number := 1828, nolines := 7, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28), (13, 1), (4, 24)] }, { number := 1825, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28), (2, 16)] }, { number := 1822, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 15996) =
      (true, 1844, hintStreamAt hints_7 16127) := by kernel_rfl

theorem p_7_485 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_485 3316501375720912038232847094038129170169639651669935147992138137664 1844 6 151516106945 1650818400321 [{ number := 1832, nolines := 7, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28), (13, 1), (10, 28)] }, { number := 1830, nolines := 7, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28), (13, 1), (5, 24)] }, { number := 1828, nolines := 7, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28), (13, 1), (4, 24)] }, { number := 1825, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28), (2, 16)] }, { number := 1822, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 16127) =
      (true, 1859, hintStreamAt hints_7 16260) := by kernel_rfl

theorem p_7_488 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_488 3316501375720912038232847094038129170169648416414409156208416292928 1862 6 277143900353 1675514462273 [{ number := 1859, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28), (13, 1)] }, { number := 1825, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28), (2, 16)] }, { number := 1822, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 16264) =
      (true, 1889, hintStreamAt hints_7 16380) := by kernel_rfl

theorem p_7_490 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_490 3316501375720912038232847094038129170169648416414400711959517610048 1890 6 8708444353 1550958657 [{ number := 1889, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28), (2, 24)] }, { number := 1859, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28), (13, 1)] }, { number := 1825, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28), (2, 16)] }, { number := 1822, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 16380) =
      (true, 1919, hintStreamAt hints_7 16496) := by kernel_rfl

theorem p_7_494 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_494 3316501375720912038232847094038129170169106817647203400911948103744 1924 6 9782186177 32689471553 [{ number := 1923, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28), (14, 28)] }, { number := 1921, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28), (7, 24)] }, { number := 1919, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28), (8, 1)] }, { number := 1889, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28), (2, 24)] }, { number := 1859, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28), (13, 1)] }, { number := 1825, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28), (2, 16)] }, { number := 1822, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 16532) =
      (true, 1951, hintStreamAt hints_7 16642) := by kernel_rfl

theorem p_7_495 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_495 3316501375720912038232847094038129170169106817646680983355173126208 1951 5 9782186177 32689471553 [{ number := 1923, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28), (14, 28)] }, { number := 1921, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28), (7, 24)] }, { number := 1919, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28), (8, 1)] }, { number := 1889, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28), (2, 24)] }, { number := 1859, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28), (13, 1)] }, { number := 1825, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28), (2, 16)] }, { number := 1822, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 16642) =
      (true, 1984, hintStreamAt hints_7 16715) := by kernel_rfl

theorem p_7_497 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_497 3316501375720912038232847094038129170169068434252448923513044451392 1985 5 235950273 24232001 [{ number := 1984, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28)] }, { number := 1822, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 16715) =
      (true, 2004, hintStreamAt hints_7 16800) := by kernel_rfl

theorem p_7_502 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_502 3316501375720912038232847094038129170169620611120557905388591398976 2012 4 34623681 410107969 [{ number := 2010, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (13, 1)] }, { number := 2008, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (13, 28)] }, { number := 2006, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (2, 16)] }, { number := 2004, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (14, 1)] }, { number := 1984, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (7, 28)] }, { number := 1822, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (4, 28), (6, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 16903) =
      (true, 2025, hintStreamAt hints_7 17044) := by kernel_rfl

theorem p_7_507 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_507 3316501375720912038232847094038128845651095060184549536601133662272 2031 5 103305409 470138945 [{ number := 2030, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (10, 1), (7, 24)] }, { number := 2025, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (4, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 17070) =
      (true, 2056, hintStreamAt hints_7 17215) := by kernel_rfl

theorem cbp_7_43 :
    evalCBPrefix 7 2 cb_7_515 (hintStreamAt hints_7 17216) =
      (true, hintStreamAt hints_7 17325) := by kernel_rfl

theorem cbp_7_44 :
    evalCBState 7 (advanceCBState 2 cb_7_515) (hintStreamAt hints_7 17325) =
      (true, hintStreamAt hints_7 17435) := by kernel_rfl

theorem cbp_7_46 :
    evalCBPrefix 7 2 cb_7_517 (hintStreamAt hints_7 17435) =
      (true, hintStreamAt hints_7 17553) := by kernel_rfl

theorem cbp_7_47 :
    evalCBState 7 (advanceCBState 2 cb_7_517) (hintStreamAt hints_7 17553) =
      (true, hintStreamAt hints_7 17650) := by kernel_rfl

theorem p_7_518 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_518 3316501375720912038232847094038128845651095060184549526018334146624 2058 6 2267566273 7986331713 [{ number := 2056, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (10, 1), (6, 28)] }, { number := 2030, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (10, 1), (7, 24)] }, { number := 2025, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (4, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 17650) =
      (true, 2059, hintStreamAt hints_7 17797) := by kernel_rfl

theorem p_7_521 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_521 3316501375720912038232847094038128845651095060184531511594054942784 2062 6 9783759041 32682393665 [{ number := 2061, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (10, 1), (7, 28), (5, 24)] }, { number := 2059, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (10, 1), (7, 28), (2, 7)] }, { number := 2056, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (10, 1), (6, 28)] }, { number := 2030, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (10, 1), (7, 24)] }, { number := 2025, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (4, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 17811) =
      (true, 2063, hintStreamAt hints_7 17960) := by kernel_rfl

theorem cbp_7_49 :
    evalCBPrefix 7 2 cb_7_527 (hintStreamAt hints_7 17966) =
      (true, hintStreamAt hints_7 18097) := by kernel_rfl

theorem cbp_7_50 :
    evalCBState 7 (advanceCBState 2 cb_7_527) (hintStreamAt hints_7 18097) =
      (true, hintStreamAt hints_7 18142) := by kernel_rfl

theorem p_7_528 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_528 3316501375720912038232847094038128845651095060184549517222241222720 2064 4 120082625 470138945 [{ number := 2056, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (10, 1), (6, 28)] }, { number := 2030, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (10, 1), (7, 24)] }, { number := 2025, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (4, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 18142) =
      (true, 2069, hintStreamAt hints_7 18259) := by kernel_rfl

theorem cbp_7_52 :
    evalCBPrefix 7 2 cb_7_535 (hintStreamAt hints_7 18259) =
      (true, hintStreamAt hints_7 18405) := by kernel_rfl

theorem cbp_7_53 :
    evalCBState 7 (advanceCBState 2 cb_7_535) (hintStreamAt hints_7 18405) =
      (true, hintStreamAt hints_7 18472) := by kernel_rfl

theorem p_7_541 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_541 3316501375720912038232847094038129170169648718644693018383674081344 2078 6 9781661889 32688422977 [{ number := 2077, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (2, 24), (7, 28), (5, 24)] }, { number := 2075, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (2, 24), (7, 28), (6, 28)] }, { number := 2071, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (7, 24)] }, { number := 2069, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (10, 1)] }, { number := 2025, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (4, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 18476) =
      (true, 2079, hintStreamAt hints_7 18597) := by kernel_rfl

theorem p_7_545 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_545 3316501375720912038232847094038129170169620911284284128100411080768 2084 6 15150371009 32688422977 [{ number := 2083, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (2, 24), (7, 28), (13, 28)] }, { number := 2081, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (2, 24), (7, 28), (11, 28)] }, { number := 2079, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (2, 24), (7, 28), (9, 30)] }, { number := 2077, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (2, 24), (7, 28), (5, 24)] }, { number := 2075, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (2, 24), (7, 28), (6, 28)] }, { number := 2071, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (7, 24)] }, { number := 2069, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (10, 1)] }, { number := 2025, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (4, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 18659) =
      (true, 2085, hintStreamAt hints_7 18721) := by kernel_rfl

theorem p_7_548 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_548 3316501375720912038232847094037547308402350410582860741418454188096 2089 5 20519080129 30540939329 [{ number := 2085, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (2, 24), (7, 28), (14, 30)] }, { number := 2083, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (2, 24), (7, 28), (13, 28)] }, { number := 2081, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (2, 24), (7, 28), (11, 28)] }, { number := 2079, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (2, 24), (7, 28), (9, 30)] }, { number := 2077, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (2, 24), (7, 28), (5, 24)] }, { number := 2075, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (2, 24), (7, 28), (6, 28)] }, { number := 2071, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (7, 24)] }, { number := 2069, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (10, 1)] }, { number := 2025, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (4, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 18795) =
      (true, 2104, hintStreamAt hints_7 18920) := by kernel_rfl

theorem p_7_554 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_554 3316501375720912038232847094038129170169648718570383615735967875136 2113 5 9764884673 32268992577 [{ number := 2111, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (2, 24), (6, 3), (11, 1)] }, { number := 2109, nolines := 6, conds := [(1, 1), (3, 1), (5, 28), (2, 24), (6, 3), (5, 24)] }, { number := 2106, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (2, 24), (6, 16)] }, { number := 2104, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (2, 24), (7, 28)] }, { number := 2071, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (7, 24)] }, { number := 2069, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (10, 1)] }, { number := 2025, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (4, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 18964) =
      (true, 2130, hintStreamAt hints_7 19114) := by kernel_rfl

theorem p_7_556 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_556 3316501375720912038232847094038129170169648718644711043390752702528 2134 4 1593537 7454785 [{ number := 2133, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (2, 24)] }, { number := 2071, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (7, 24)] }, { number := 2069, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (10, 1)] }, { number := 2025, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (4, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 19123) =
      (true, 2147, hintStreamAt hints_7 19209) := by kernel_rfl

theorem cbp_7_55 :
    evalCBPrefix 7 1 cb_7_564 (hintStreamAt hints_7 19210) =
      (true, hintStreamAt hints_7 19304) := by kernel_rfl

theorem cbp_7_56 :
    evalCBState 7 (advanceCBState 1 cb_7_564) (hintStreamAt hints_7 19304) =
      (true, hintStreamAt hints_7 19389) := by kernel_rfl

theorem p_7_566 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_566 3316501375720912038232847094038129170169648718644702588532882161728 2151 5 136073409 24232001 [{ number := 2150, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (7, 28), (5, 24)] }, { number := 2147, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (6, 28)] }, { number := 2133, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (2, 24)] }, { number := 2071, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (7, 24)] }, { number := 2069, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (10, 1)] }, { number := 2025, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (4, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 19389) =
      (true, 2152, hintStreamAt hints_7 19492) := by kernel_rfl

theorem cbp_7_58 :
    evalCBPrefix 7 3 cb_7_575 (hintStreamAt hints_7 19592) =
      (true, hintStreamAt hints_7 19739) := by kernel_rfl

theorem cbp_7_59 :
    evalCBState 7 (advanceCBState 3 cb_7_575) (hintStreamAt hints_7 19739) =
      (true, hintStreamAt hints_7 19746) := by kernel_rfl

theorem p_7_576 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_576 3316501375720912038232847094038129170169648718644692173958743867456 2156 4 136073409 57786433 [{ number := 2154, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (7, 28), (9, 1)] }, { number := 2152, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (7, 28), (8, 1)] }, { number := 2150, nolines := 5, conds := [(1, 1), (3, 1), (5, 28), (7, 28), (5, 24)] }, { number := 2147, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (6, 28)] }, { number := 2133, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (2, 24)] }, { number := 2071, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (7, 24)] }, { number := 2069, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (10, 1)] }, { number := 2025, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (4, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 19746) =
      (true, 2161, hintStreamAt hints_7 19878) := by kernel_rfl

theorem p_7_578 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_578 3316501375720912038232847094038129170169648718644702579762558943296 2162 4 2117825 376897 [{ number := 2161, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (7, 28)] }, { number := 2147, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (6, 28)] }, { number := 2133, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (2, 24)] }, { number := 2071, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (7, 24)] }, { number := 2069, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (10, 1)] }, { number := 2025, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (4, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 19878) =
      (true, 2163, hintStreamAt hints_7 19982) := by kernel_rfl

theorem p_7_579 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_579 3316501375720912038232847094038129170169648718644710742536883552320 2163 3 2117825 376897 [{ number := 2161, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (7, 28)] }, { number := 2147, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (6, 28)] }, { number := 2133, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (2, 24)] }, { number := 2071, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (7, 24)] }, { number := 2069, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (10, 1)] }, { number := 2025, nolines := 4, conds := [(1, 1), (3, 1), (5, 28), (4, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 19982) =
      (true, 2166, hintStreamAt hints_7 20125) := by kernel_rfl

theorem cbp_7_61 :
    evalCBPrefix 7 8 cb_7_588 (hintStreamAt hints_7 20143) =
      (true, hintStreamAt hints_7 20283) := by kernel_rfl

theorem cbp_7_62 :
    evalCBState 7 (advanceCBState 8 cb_7_588) (hintStreamAt hints_7 20283) =
      (true, hintStreamAt hints_7 20351) := by kernel_rfl

theorem p_7_590 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_590 3316501375720912038232847094038129170169648576974869582544864854080 2172 4 1097921 6295617 [{ number := 2171, nolines := 4, conds := [(1, 1), (3, 1), (12, 1), (2, 16)] }, { number := 2168, nolines := 3, conds := [(1, 1), (3, 1), (6, 28)] }, { number := 2166, nolines := 3, conds := [(1, 1), (3, 1), (5, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 20351) =
      (true, 2173, hintStreamAt hints_7 20461) := by kernel_rfl

theorem p_7_591 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_591 3316501375720912038232847094038129170169648576974869582544562864192 2173 3 1097921 6295617 [{ number := 2171, nolines := 4, conds := [(1, 1), (3, 1), (12, 1), (2, 16)] }, { number := 2168, nolines := 3, conds := [(1, 1), (3, 1), (6, 28)] }, { number := 2166, nolines := 3, conds := [(1, 1), (3, 1), (5, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 20461) =
      (true, 2180, hintStreamAt hints_7 20611) := by kernel_rfl

theorem p_7_596 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_596 3316501375720912038232847094038129170169648713849710600673275772992 2185 5 34648257 403562561 [{ number := 2184, nolines := 5, conds := [(1, 1), (3, 1), (11, 30), (4, 3), (7, 3)] }, { number := 2180, nolines := 3, conds := [(1, 1), (3, 1), (12, 1)] }, { number := 2168, nolines := 3, conds := [(1, 1), (3, 1), (6, 28)] }, { number := 2166, nolines := 3, conds := [(1, 1), (3, 1), (5, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 20612) =
      (true, 2202, hintStreamAt hints_7 20721) := by kernel_rfl

theorem p_7_597 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_597 3316501375720912038232847094038129170169648713849710600673275691072 2202 4 34648257 403562561 [{ number := 2184, nolines := 5, conds := [(1, 1), (3, 1), (11, 30), (4, 3), (7, 3)] }, { number := 2180, nolines := 3, conds := [(1, 1), (3, 1), (12, 1)] }, { number := 2168, nolines := 3, conds := [(1, 1), (3, 1), (6, 28)] }, { number := 2166, nolines := 3, conds := [(1, 1), (3, 1), (5, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 20721) =
      (true, 2209, hintStreamAt hints_7 20847) := by kernel_rfl

theorem p_7_599 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_599 3316501375720912038232847094038129170169648713849710583081525952576 2210 4 1880257 6414401 [{ number := 2209, nolines := 4, conds := [(1, 1), (3, 1), (11, 30), (4, 3)] }, { number := 2180, nolines := 3, conds := [(1, 1), (3, 1), (12, 1)] }, { number := 2168, nolines := 3, conds := [(1, 1), (3, 1), (6, 28)] }, { number := 2166, nolines := 3, conds := [(1, 1), (3, 1), (5, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 20847) =
      (true, 2219, hintStreamAt hints_7 20934) := by kernel_rfl

theorem p_7_602 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_602 3316501375720912038232847094038129170169639646906063394197811347520 2221 5 70561985 403038273 [{ number := 2219, nolines := 4, conds := [(1, 1), (3, 1), (11, 30), (7, 24)] }, { number := 2209, nolines := 4, conds := [(1, 1), (3, 1), (11, 30), (4, 3)] }, { number := 2180, nolines := 3, conds := [(1, 1), (3, 1), (12, 1)] }, { number := 2168, nolines := 3, conds := [(1, 1), (3, 1), (6, 28)] }, { number := 2166, nolines := 3, conds := [(1, 1), (3, 1), (5, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 20934) =
      (true, 2222, hintStreamAt hints_7 21004) := by kernel_rfl

theorem p_7_603 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_603 3316501375720912038232847094038129170169639646906063394197475803200 2222 4 70561985 403038273 [{ number := 2219, nolines := 4, conds := [(1, 1), (3, 1), (11, 30), (7, 24)] }, { number := 2209, nolines := 4, conds := [(1, 1), (3, 1), (11, 30), (4, 3)] }, { number := 2180, nolines := 3, conds := [(1, 1), (3, 1), (12, 1)] }, { number := 2168, nolines := 3, conds := [(1, 1), (3, 1), (6, 28)] }, { number := 2166, nolines := 3, conds := [(1, 1), (3, 1), (5, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 21004) =
      (true, 2233, hintStreamAt hints_7 21146) := by kernel_rfl

theorem p_7_609 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_609 3316501375720912038232847094038119434613038658781864451644076638272 2241 5 172536001 17162305 [{ number := 2239, nolines := 4, conds := [(1, 1), (3, 1), (11, 30), (2, 16)] }, { number := 2237, nolines := 4, conds := [(1, 1), (3, 1), (11, 30), (7, 3)] }, { number := 2235, nolines := 4, conds := [(1, 1), (3, 1), (11, 30), (4, 24)] }, { number := 2233, nolines := 4, conds := [(1, 1), (3, 1), (11, 30), (13, 1)] }, { number := 2219, nolines := 4, conds := [(1, 1), (3, 1), (11, 30), (7, 24)] }, { number := 2209, nolines := 4, conds := [(1, 1), (3, 1), (11, 30), (4, 3)] }, { number := 2180, nolines := 3, conds := [(1, 1), (3, 1), (12, 1)] }, { number := 2168, nolines := 3, conds := [(1, 1), (3, 1), (6, 28)] }, { number := 2166, nolines := 3, conds := [(1, 1), (3, 1), (5, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 21150) =
      (true, 2242, hintStreamAt hints_7 21272) := by kernel_rfl

theorem p_7_610 :
    verifyTreePureRec 7 shiftedOutsTable_7 n_7_610 3316501375720912038232847094038119434613038658815299175277675200576 2242 4 172536001 17162305 [{ number := 2239, nolines := 4, conds := [(1, 1), (3, 1), (11, 30), (2, 16)] }, { number := 2237, nolines := 4, conds := [(1, 1), (3, 1), (11, 30), (7, 3)] }, { number := 2235, nolines := 4, conds := [(1, 1), (3, 1), (11, 30), (4, 24)] }, { number := 2233, nolines := 4, conds := [(1, 1), (3, 1), (11, 30), (13, 1)] }, { number := 2219, nolines := 4, conds := [(1, 1), (3, 1), (11, 30), (7, 24)] }, { number := 2209, nolines := 4, conds := [(1, 1), (3, 1), (11, 30), (4, 3)] }, { number := 2180, nolines := 3, conds := [(1, 1), (3, 1), (12, 1)] }, { number := 2168, nolines := 3, conds := [(1, 1), (3, 1), (6, 28)] }, { number := 2166, nolines := 3, conds := [(1, 1), (3, 1), (5, 28)] }, { number := 1730, nolines := 3, conds := [(1, 1), (3, 1), (2, 3)] }, { number := 1362, nolines := 3, conds := [(1, 1), (3, 1), (6, 1)] }, { number := 1360, nolines := 3, conds := [(1, 1), (3, 1), (5, 1)] }, { number := 968, nolines := 3, conds := [(1, 1), (3, 1), (4, 1)] }, { number := 965, nolines := 2, conds := [(1, 1), (7, 1)] }, { number := 963, nolines := 2, conds := [(1, 1), (2, 1)] }] (hintStreamAt hints_7 21272) =
      (true, 2247, hintStreamAt hints_7 21313) := by kernel_rfl

end Math.Discharging
