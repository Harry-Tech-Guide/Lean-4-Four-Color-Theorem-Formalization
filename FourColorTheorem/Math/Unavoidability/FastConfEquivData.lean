module

/-
Copyright (c) 2026 Four Color Theorem Formalization Project.
Released under Apache 2.0 license.
-/
public import FourColorTheorem.Math.Unavoidability.FastConfEquivBase

@[expose] public section

/-!
# 633-Configuration `RConf` ↔ `FastConf` Block/Row Indexing Table
-/

namespace Math.Unavoidability

open Math Math.Discharging Internal
/-! ## 80-Row Explicit Table (`rc_0` .. `rc_632`) -/

def rcRow_0_0 : List FastReducer.RConf := [rc_0, rc_1, rc_2, rc_3, rc_4, rc_5, rc_6, rc_7]
def rcRow_0_1 : List FastReducer.RConf := [rc_8, rc_9, rc_10, rc_11, rc_12, rc_13, rc_14, rc_15]
def rcRow_0_2 : List FastReducer.RConf := [rc_16, rc_17, rc_18, rc_19, rc_20, rc_21, rc_22, rc_23]
def rcRow_0_3 : List FastReducer.RConf := [rc_24, rc_25, rc_26, rc_27, rc_28, rc_29, rc_30, rc_31]
def rcRow_0_4 : List FastReducer.RConf := [rc_32, rc_33, rc_34, rc_35, rc_36, rc_37, rc_38, rc_39]
def rcRow_0_5 : List FastReducer.RConf := [rc_40, rc_41, rc_42, rc_43, rc_44, rc_45, rc_46, rc_47]
def rcRow_0_6 : List FastReducer.RConf := [rc_48, rc_49, rc_50, rc_51, rc_52, rc_53, rc_54, rc_55]
def rcRow_0_7 : List FastReducer.RConf := [rc_56, rc_57, rc_58, rc_59, rc_60, rc_61, rc_62, rc_63]

def rcRow_1_0 : List FastReducer.RConf := [rc_64, rc_65, rc_66, rc_67, rc_68, rc_69, rc_70, rc_71]
def rcRow_1_1 : List FastReducer.RConf := [rc_72, rc_73, rc_74, rc_75, rc_76, rc_77, rc_78, rc_79]
def rcRow_1_2 : List FastReducer.RConf := [rc_80, rc_81, rc_82, rc_83, rc_84, rc_85, rc_86, rc_87]
def rcRow_1_3 : List FastReducer.RConf := [rc_88, rc_89, rc_90, rc_91, rc_92, rc_93, rc_94, rc_95]
def rcRow_1_4 : List FastReducer.RConf := [rc_96, rc_97, rc_98, rc_99, rc_100, rc_101, rc_102, rc_103]
def rcRow_1_5 : List FastReducer.RConf := [rc_104, rc_105, rc_106, rc_107, rc_108, rc_109, rc_110, rc_111]
def rcRow_1_6 : List FastReducer.RConf := [rc_112, rc_113, rc_114, rc_115, rc_116, rc_117, rc_118, rc_119]
def rcRow_1_7 : List FastReducer.RConf := [rc_120, rc_121, rc_122, rc_123, rc_124, rc_125, rc_126, rc_127]

def rcRow_2_0 : List FastReducer.RConf := [rc_128, rc_129, rc_130, rc_131, rc_132, rc_133, rc_134, rc_135]
def rcRow_2_1 : List FastReducer.RConf := [rc_136, rc_137, rc_138, rc_139, rc_140, rc_141, rc_142, rc_143]
def rcRow_2_2 : List FastReducer.RConf := [rc_144, rc_145, rc_146, rc_147, rc_148, rc_149, rc_150, rc_151]
def rcRow_2_3 : List FastReducer.RConf := [rc_152, rc_153, rc_154, rc_155, rc_156, rc_157, rc_158, rc_159]
def rcRow_2_4 : List FastReducer.RConf := [rc_160, rc_161, rc_162, rc_163, rc_164, rc_165, rc_166, rc_167]
def rcRow_2_5 : List FastReducer.RConf := [rc_168, rc_169, rc_170, rc_171, rc_172, rc_173, rc_174, rc_175]
def rcRow_2_6 : List FastReducer.RConf := [rc_176, rc_177, rc_178, rc_179, rc_180, rc_181, rc_182, rc_183]
def rcRow_2_7 : List FastReducer.RConf := [rc_184, rc_185, rc_186, rc_187, rc_188, rc_189, rc_190, rc_191]

def rcRow_3_0 : List FastReducer.RConf := [rc_192, rc_193, rc_194, rc_195, rc_196, rc_197, rc_198, rc_199]
def rcRow_3_1 : List FastReducer.RConf := [rc_200, rc_201, rc_202, rc_203, rc_204, rc_205, rc_206, rc_207]
def rcRow_3_2 : List FastReducer.RConf := [rc_208, rc_209, rc_210, rc_211, rc_212, rc_213, rc_214, rc_215]
def rcRow_3_3 : List FastReducer.RConf := [rc_216, rc_217, rc_218, rc_219, rc_220, rc_221, rc_222, rc_223]
def rcRow_3_4 : List FastReducer.RConf := [rc_224, rc_225, rc_226, rc_227, rc_228, rc_229, rc_230, rc_231]
def rcRow_3_5 : List FastReducer.RConf := [rc_232, rc_233, rc_234, rc_235, rc_236, rc_237, rc_238, rc_239]
def rcRow_3_6 : List FastReducer.RConf := [rc_240, rc_241, rc_242, rc_243, rc_244, rc_245, rc_246, rc_247]
def rcRow_3_7 : List FastReducer.RConf := [rc_248, rc_249, rc_250, rc_251, rc_252, rc_253, rc_254, rc_255]

def rcRow_4_0 : List FastReducer.RConf := [rc_256, rc_257, rc_258, rc_259, rc_260, rc_261, rc_262, rc_263]
def rcRow_4_1 : List FastReducer.RConf := [rc_264, rc_265, rc_266, rc_267, rc_268, rc_269, rc_270, rc_271]
def rcRow_4_2 : List FastReducer.RConf := [rc_272, rc_273, rc_274, rc_275, rc_276, rc_277, rc_278, rc_279]
def rcRow_4_3 : List FastReducer.RConf := [rc_280, rc_281, rc_282, rc_283, rc_284, rc_285, rc_286, rc_287]
def rcRow_4_4 : List FastReducer.RConf := [rc_288, rc_289, rc_290, rc_291, rc_292, rc_293, rc_294, rc_295]
def rcRow_4_5 : List FastReducer.RConf := [rc_296, rc_297, rc_298, rc_299, rc_300, rc_301, rc_302, rc_303]
def rcRow_4_6 : List FastReducer.RConf := [rc_304, rc_305, rc_306, rc_307, rc_308, rc_309, rc_310, rc_311]
def rcRow_4_7 : List FastReducer.RConf := [rc_312, rc_313, rc_314, rc_315, rc_316, rc_317, rc_318, rc_319]

def rcRow_5_0 : List FastReducer.RConf := [rc_320, rc_321, rc_322, rc_323, rc_324, rc_325, rc_326, rc_327]
def rcRow_5_1 : List FastReducer.RConf := [rc_328, rc_329, rc_330, rc_331, rc_332, rc_333, rc_334, rc_335]
def rcRow_5_2 : List FastReducer.RConf := [rc_336, rc_337, rc_338, rc_339, rc_340, rc_341, rc_342, rc_343]
def rcRow_5_3 : List FastReducer.RConf := [rc_344, rc_345, rc_346, rc_347, rc_348, rc_349, rc_350, rc_351]
def rcRow_5_4 : List FastReducer.RConf := [rc_352, rc_353, rc_354, rc_355, rc_356, rc_357, rc_358, rc_359]
def rcRow_5_5 : List FastReducer.RConf := [rc_360, rc_361, rc_362, rc_363, rc_364, rc_365, rc_366, rc_367]
def rcRow_5_6 : List FastReducer.RConf := [rc_368, rc_369, rc_370, rc_371, rc_372, rc_373, rc_374, rc_375]
def rcRow_5_7 : List FastReducer.RConf := [rc_376, rc_377, rc_378, rc_379, rc_380, rc_381, rc_382, rc_383]

def rcRow_6_0 : List FastReducer.RConf := [rc_384, rc_385, rc_386, rc_387, rc_388, rc_389, rc_390, rc_391]
def rcRow_6_1 : List FastReducer.RConf := [rc_392, rc_393, rc_394, rc_395, rc_396, rc_397, rc_398, rc_399]
def rcRow_6_2 : List FastReducer.RConf := [rc_400, rc_401, rc_402, rc_403, rc_404, rc_405, rc_406, rc_407]
def rcRow_6_3 : List FastReducer.RConf := [rc_408, rc_409, rc_410, rc_411, rc_412, rc_413, rc_414, rc_415]
def rcRow_6_4 : List FastReducer.RConf := [rc_416, rc_417, rc_418, rc_419, rc_420, rc_421, rc_422, rc_423]
def rcRow_6_5 : List FastReducer.RConf := [rc_424, rc_425, rc_426, rc_427, rc_428, rc_429, rc_430, rc_431]
def rcRow_6_6 : List FastReducer.RConf := [rc_432, rc_433, rc_434, rc_435, rc_436, rc_437, rc_438, rc_439]
def rcRow_6_7 : List FastReducer.RConf := [rc_440, rc_441, rc_442, rc_443, rc_444, rc_445, rc_446, rc_447]

def rcRow_7_0 : List FastReducer.RConf := [rc_448, rc_449, rc_450, rc_451, rc_452, rc_453, rc_454, rc_455]
def rcRow_7_1 : List FastReducer.RConf := [rc_456, rc_457, rc_458, rc_459, rc_460, rc_461, rc_462, rc_463]
def rcRow_7_2 : List FastReducer.RConf := [rc_464, rc_465, rc_466, rc_467, rc_468, rc_469, rc_470, rc_471]
def rcRow_7_3 : List FastReducer.RConf := [rc_472, rc_473, rc_474, rc_475, rc_476, rc_477, rc_478, rc_479]
def rcRow_7_4 : List FastReducer.RConf := [rc_480, rc_481, rc_482, rc_483, rc_484, rc_485, rc_486, rc_487]
def rcRow_7_5 : List FastReducer.RConf := [rc_488, rc_489, rc_490, rc_491, rc_492, rc_493, rc_494, rc_495]
def rcRow_7_6 : List FastReducer.RConf := [rc_496, rc_497, rc_498, rc_499, rc_500, rc_501, rc_502, rc_503]
def rcRow_7_7 : List FastReducer.RConf := [rc_504, rc_505, rc_506, rc_507, rc_508, rc_509, rc_510, rc_511]

def rcRow_8_0 : List FastReducer.RConf := [rc_512, rc_513, rc_514, rc_515, rc_516, rc_517, rc_518, rc_519]
def rcRow_8_1 : List FastReducer.RConf := [rc_520, rc_521, rc_522, rc_523, rc_524, rc_525, rc_526, rc_527]
def rcRow_8_2 : List FastReducer.RConf := [rc_528, rc_529, rc_530, rc_531, rc_532, rc_533, rc_534, rc_535]
def rcRow_8_3 : List FastReducer.RConf := [rc_536, rc_537, rc_538, rc_539, rc_540, rc_541, rc_542, rc_543]
def rcRow_8_4 : List FastReducer.RConf := [rc_544, rc_545, rc_546, rc_547, rc_548, rc_549, rc_550, rc_551]
def rcRow_8_5 : List FastReducer.RConf := [rc_552, rc_553, rc_554, rc_555, rc_556, rc_557, rc_558, rc_559]
def rcRow_8_6 : List FastReducer.RConf := [rc_560, rc_561, rc_562, rc_563, rc_564, rc_565, rc_566, rc_567]
def rcRow_8_7 : List FastReducer.RConf := [rc_568, rc_569, rc_570, rc_571, rc_572, rc_573, rc_574, rc_575]

def rcRow_9_0 : List FastReducer.RConf := [rc_576, rc_577, rc_578, rc_579, rc_580, rc_581, rc_582, rc_583]
def rcRow_9_1 : List FastReducer.RConf := [rc_584, rc_585, rc_586, rc_587, rc_588, rc_589, rc_590, rc_591]
def rcRow_9_2 : List FastReducer.RConf := [rc_592, rc_593, rc_594, rc_595, rc_596, rc_597, rc_598, rc_599]
def rcRow_9_3 : List FastReducer.RConf := [rc_600, rc_601, rc_602, rc_603, rc_604, rc_605, rc_606, rc_607]
def rcRow_9_4 : List FastReducer.RConf := [rc_608, rc_609, rc_610, rc_611, rc_612, rc_613, rc_614, rc_615]
def rcRow_9_5 : List FastReducer.RConf := [rc_616, rc_617, rc_618, rc_619, rc_620, rc_621, rc_622, rc_623]
def rcRow_9_6 : List FastReducer.RConf := [rc_624, rc_625, rc_626, rc_627, rc_628, rc_629, rc_630, rc_631]
def rcRow_9_7 : List FastReducer.RConf := [rc_632]

def rcBlk_0 : List (List FastReducer.RConf) := [rcRow_0_0, rcRow_0_1, rcRow_0_2, rcRow_0_3, rcRow_0_4, rcRow_0_5, rcRow_0_6, rcRow_0_7]
def rcBlk_1 : List (List FastReducer.RConf) := [rcRow_1_0, rcRow_1_1, rcRow_1_2, rcRow_1_3, rcRow_1_4, rcRow_1_5, rcRow_1_6, rcRow_1_7]
def rcBlk_2 : List (List FastReducer.RConf) := [rcRow_2_0, rcRow_2_1, rcRow_2_2, rcRow_2_3, rcRow_2_4, rcRow_2_5, rcRow_2_6, rcRow_2_7]
def rcBlk_3 : List (List FastReducer.RConf) := [rcRow_3_0, rcRow_3_1, rcRow_3_2, rcRow_3_3, rcRow_3_4, rcRow_3_5, rcRow_3_6, rcRow_3_7]
def rcBlk_4 : List (List FastReducer.RConf) := [rcRow_4_0, rcRow_4_1, rcRow_4_2, rcRow_4_3, rcRow_4_4, rcRow_4_5, rcRow_4_6, rcRow_4_7]
def rcBlk_5 : List (List FastReducer.RConf) := [rcRow_5_0, rcRow_5_1, rcRow_5_2, rcRow_5_3, rcRow_5_4, rcRow_5_5, rcRow_5_6, rcRow_5_7]
def rcBlk_6 : List (List FastReducer.RConf) := [rcRow_6_0, rcRow_6_1, rcRow_6_2, rcRow_6_3, rcRow_6_4, rcRow_6_5, rcRow_6_6, rcRow_6_7]
def rcBlk_7 : List (List FastReducer.RConf) := [rcRow_7_0, rcRow_7_1, rcRow_7_2, rcRow_7_3, rcRow_7_4, rcRow_7_5, rcRow_7_6, rcRow_7_7]
def rcBlk_8 : List (List FastReducer.RConf) := [rcRow_8_0, rcRow_8_1, rcRow_8_2, rcRow_8_3, rcRow_8_4, rcRow_8_5, rcRow_8_6, rcRow_8_7]
def rcBlk_9 : List (List FastReducer.RConf) := [rcRow_9_0, rcRow_9_1, rcRow_9_2, rcRow_9_3, rcRow_9_4, rcRow_9_5, rcRow_9_6, rcRow_9_7]

def rcTable : List (List (List FastReducer.RConf)) := [rcBlk_0, rcBlk_1, rcBlk_2, rcBlk_3, rcBlk_4, rcBlk_5, rcBlk_6, rcBlk_7, rcBlk_8, rcBlk_9]

theorem fcBlk_0_len : Discharging.fcBlk_0.length = 8 := rfl
theorem fcBlk_0_row_lens : Discharging.fcBlk_0.map List.length = List.replicate 8 8 := rfl
theorem rcBlk_0_len : rcBlk_0.length = 8 := rfl
theorem rcBlk_0_row_lens : rcBlk_0.map List.length = List.replicate 8 8 := rfl
theorem rcBlk_0_flat_len : rcBlk_0.flatten.length = 64 := rfl
theorem fcBlk_1_len : Discharging.fcBlk_1.length = 8 := rfl
theorem fcBlk_1_row_lens : Discharging.fcBlk_1.map List.length = List.replicate 8 8 := rfl
theorem rcBlk_1_len : rcBlk_1.length = 8 := rfl
theorem rcBlk_1_row_lens : rcBlk_1.map List.length = List.replicate 8 8 := rfl
theorem rcBlk_1_flat_len : rcBlk_1.flatten.length = 64 := rfl
theorem fcBlk_2_len : Discharging.fcBlk_2.length = 8 := rfl
theorem fcBlk_2_row_lens : Discharging.fcBlk_2.map List.length = List.replicate 8 8 := rfl
theorem rcBlk_2_len : rcBlk_2.length = 8 := rfl
theorem rcBlk_2_row_lens : rcBlk_2.map List.length = List.replicate 8 8 := rfl
theorem rcBlk_2_flat_len : rcBlk_2.flatten.length = 64 := rfl
theorem fcBlk_3_len : Discharging.fcBlk_3.length = 8 := rfl
theorem fcBlk_3_row_lens : Discharging.fcBlk_3.map List.length = List.replicate 8 8 := rfl
theorem rcBlk_3_len : rcBlk_3.length = 8 := rfl
theorem rcBlk_3_row_lens : rcBlk_3.map List.length = List.replicate 8 8 := rfl
theorem rcBlk_3_flat_len : rcBlk_3.flatten.length = 64 := rfl
theorem fcBlk_4_len : Discharging.fcBlk_4.length = 8 := rfl
theorem fcBlk_4_row_lens : Discharging.fcBlk_4.map List.length = List.replicate 8 8 := rfl
theorem rcBlk_4_len : rcBlk_4.length = 8 := rfl
theorem rcBlk_4_row_lens : rcBlk_4.map List.length = List.replicate 8 8 := rfl
theorem rcBlk_4_flat_len : rcBlk_4.flatten.length = 64 := rfl
theorem fcBlk_5_len : Discharging.fcBlk_5.length = 8 := rfl
theorem fcBlk_5_row_lens : Discharging.fcBlk_5.map List.length = List.replicate 8 8 := rfl
theorem rcBlk_5_len : rcBlk_5.length = 8 := rfl
theorem rcBlk_5_row_lens : rcBlk_5.map List.length = List.replicate 8 8 := rfl
theorem rcBlk_5_flat_len : rcBlk_5.flatten.length = 64 := rfl
theorem fcBlk_6_len : Discharging.fcBlk_6.length = 8 := rfl
theorem fcBlk_6_row_lens : Discharging.fcBlk_6.map List.length = List.replicate 8 8 := rfl
theorem rcBlk_6_len : rcBlk_6.length = 8 := rfl
theorem rcBlk_6_row_lens : rcBlk_6.map List.length = List.replicate 8 8 := rfl
theorem rcBlk_6_flat_len : rcBlk_6.flatten.length = 64 := rfl
theorem fcBlk_7_len : Discharging.fcBlk_7.length = 8 := rfl
theorem fcBlk_7_row_lens : Discharging.fcBlk_7.map List.length = List.replicate 8 8 := rfl
theorem rcBlk_7_len : rcBlk_7.length = 8 := rfl
theorem rcBlk_7_row_lens : rcBlk_7.map List.length = List.replicate 8 8 := rfl
theorem rcBlk_7_flat_len : rcBlk_7.flatten.length = 64 := rfl
theorem fcBlk_8_len : Discharging.fcBlk_8.length = 8 := rfl
theorem fcBlk_8_row_lens : Discharging.fcBlk_8.map List.length = List.replicate 8 8 := rfl
theorem rcBlk_8_len : rcBlk_8.length = 8 := rfl
theorem rcBlk_8_row_lens : rcBlk_8.map List.length = List.replicate 8 8 := rfl
theorem rcBlk_8_flat_len : rcBlk_8.flatten.length = 64 := rfl
theorem fcBlk_9_len : Discharging.fcBlk_9.length = 8 := rfl
theorem fcBlk_9_row_lens : Discharging.fcBlk_9.map List.length = List.replicate 8 8 := rfl
theorem rcBlk_9_len : rcBlk_9.length = 8 := rfl
theorem rcBlk_9_row_lens : rcBlk_9.map List.length = List.replicate 7 8 ++ [1] := rfl
theorem rcBlk_9_flat_len : rcBlk_9.flatten.length = 57 := rfl
theorem fastConfTable_len : Discharging.fastConfTable.length = 10 := rfl
theorem rcTable_len : rcTable.length = 10 := rfl

private def rcFlatBlocks : List (List FastReducer.RConf) :=
  [rcBlk_0.flatten, rcBlk_1.flatten, rcBlk_2.flatten, rcBlk_3.flatten, rcBlk_4.flatten,
   rcBlk_5.flatten, rcBlk_6.flatten, rcBlk_7.flatten, rcBlk_8.flatten, rcBlk_9.flatten]

private theorem rcFlatBlocks_len : rcFlatBlocks.length = 10 := rfl

private def pDrop1 : List FastReducer.RConf := parsedRConfList.drop 128
private def pDrop2 : List FastReducer.RConf := pDrop1.drop 128
private def pDrop3 : List FastReducer.RConf := pDrop2.drop 128
private def pDrop4 : List FastReducer.RConf := pDrop3.drop 128

set_option maxRecDepth 200000 in
private theorem chunk0_eq : parsedRConfList.take 128 = rcBlk_0.flatten ++ rcBlk_1.flatten := rfl
set_option maxRecDepth 200000 in
private theorem chunk1_eq : pDrop1.take 128 = rcBlk_2.flatten ++ rcBlk_3.flatten := rfl
set_option maxRecDepth 200000 in
private theorem chunk2_eq : pDrop2.take 128 = rcBlk_4.flatten ++ rcBlk_5.flatten := rfl
set_option maxRecDepth 200000 in
private theorem chunk3_eq : pDrop3.take 128 = rcBlk_6.flatten ++ rcBlk_7.flatten := rfl
set_option maxRecDepth 200000 in
private theorem chunk4_eq : pDrop4 = rcBlk_8.flatten ++ rcBlk_9.flatten := rfl

private theorem parsedRConfList_chunks_eq :
    parsedRConfList =
      parsedRConfList.take 128 ++ (pDrop1.take 128 ++ (pDrop2.take 128 ++ (pDrop3.take 128 ++ pDrop4))) := by
  have h4 : pDrop3.take 128 ++ pDrop4 = pDrop3 := List.take_append_drop 128 pDrop3
  have h3 : pDrop2.take 128 ++ pDrop3 = pDrop2 := List.take_append_drop 128 pDrop2
  have h2 : pDrop1.take 128 ++ pDrop2 = pDrop1 := List.take_append_drop 128 pDrop1
  have h1 : parsedRConfList.take 128 ++ pDrop1 = parsedRConfList := List.take_append_drop 128 parsedRConfList
  rw [h4, h3, h2, h1]

private theorem list_append_eq {α : Type} (a b : List α) : a.append b = a ++ b := rfl

private theorem rcFlatBlocks_flatten_eq : rcFlatBlocks.flatten = parsedRConfList := by
  rw [parsedRConfList_chunks_eq, chunk0_eq, chunk1_eq, chunk2_eq, chunk3_eq, chunk4_eq]
  simp only [rcFlatBlocks, List.flatten, list_append_eq, List.append_nil, List.append_assoc]

/-- Length of `parsedRConfList` equals `633`. -/
theorem parsedRConfList_length : parsedRConfList.length = 633 := by
  rw [← rcFlatBlocks_flatten_eq, List.length_flatten]
  simp only [rcFlatBlocks, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    rcBlk_0_flat_len, rcBlk_1_flat_len, rcBlk_2_flat_len, rcBlk_3_flat_len,
    rcBlk_4_flat_len, rcBlk_5_flat_len, rcBlk_6_flat_len, rcBlk_7_flat_len,
    rcBlk_8_flat_len, rcBlk_9_flat_len]
  decide

/-- Size of `theUnavoidableSet` equals `633`. -/
theorem theUnavoidableSet_size : theUnavoidableSet.size = 633 := by
  simp [theUnavoidableSet, parsedRConfList_length]

/-- Indexing into `theUnavoidableSet` yields `configOfRConf` on `parsedRConfList`. -/
theorem theUnavoidableSet_getElem (h : Nat) (hh : h < 633) :
    theUnavoidableSet[h]'(by rw [theUnavoidableSet_size]; exact hh) =
      configOfRConf (parsedRConfList[h]'(by rw [parsedRConfList_length]; exact hh)) := by
  simp [theUnavoidableSet]

private theorem map_len_replicate_8 {α : Type} (xs : List (List α))
    (h : xs.map List.length = List.replicate 8 8) :
    ∀ r, r < 8 → ∃ hrx : r < xs.length, (xs[r]'hrx).length = 8 := by
  have hlen : xs.length = 8 := by have := congrArg List.length h; simpa using this
  intro r hr
  have hrx : r < xs.length := by omega
  refine ⟨hrx, ?_⟩
  have he : (xs.map List.length)[r]? = (List.replicate 8 8)[r]? := by rw [h]
  have h1 : (xs.map List.length)[r]? = some (xs[r]'hrx).length := by simp [hrx]
  have h2 : (List.replicate 8 8)[r]? = some 8 := by rw [List.getElem?_replicate]; simp [hr]
  rw [h1, h2] at he
  exact Option.some.inj he

private theorem map_len_rcBlk_9 :
    ∀ r, r < 8 →
      ∃ hrx : r < rcBlk_9.length,
        (rcBlk_9[r]'hrx).length = (if r < 7 then 8 else 1) := by
  intro r hr
  have hrx : r < rcBlk_9.length := by rw [rcBlk_9_len]; exact hr
  refine ⟨hrx, ?_⟩
  have he : (rcBlk_9.map List.length)[r]? = (List.replicate 7 8 ++ [1])[r]? := by rw [rcBlk_9_row_lens]
  have h1 : (rcBlk_9.map List.length)[r]? = some (rcBlk_9[r]'hrx).length := by simp [hrx]
  rw [h1] at he
  by_cases hr7 : r < 7
  · have ha : r < (List.replicate 7 8).length := by simp [hr7]
    have h2 : (List.replicate 7 8 ++ [1])[r]? = some 8 := by
      rw [List.getElem?_append_left ha, List.getElem?_replicate]
      simp [hr7]
    rw [h2] at he
    simpa [hr7] using Option.some.inj he
  · have hr_eq : r = 7 := by omega
    subst hr_eq
    have ha : (List.replicate 7 8).length ≤ 7 := by simp
    have h2 : (List.replicate 7 8 ++ [1])[7]? = some 1 := by
      rw [List.getElem?_append_right ha]; simp
    rw [h2] at he
    simpa using Option.some.inj he

theorem fcTable_row_len (b : Nat) (hb : b < 10) :
    (Discharging.fastConfTable[b]'(by rw [fastConfTable_len]; exact hb)).length = 8 := by
  match b with
  | 0 => exact fcBlk_0_len
  | 1 => exact fcBlk_1_len
  | 2 => exact fcBlk_2_len
  | 3 => exact fcBlk_3_len
  | 4 => exact fcBlk_4_len
  | 5 => exact fcBlk_5_len
  | 6 => exact fcBlk_6_len
  | 7 => exact fcBlk_7_len
  | 8 => exact fcBlk_8_len
  | 9 => exact fcBlk_9_len
  | _ + 10 => omega

theorem fcTable_cell_len (b r : Nat) (hb : b < 10) (hr : r < 8) :
    ((Discharging.fastConfTable[b]'(by rw [fastConfTable_len]; exact hb))[r]'(by
      rw [fcTable_row_len b hb]; exact hr)).length = 8 := by
  match b with
  | 0 => exact (map_len_replicate_8 _ fcBlk_0_row_lens r hr).2
  | 1 => exact (map_len_replicate_8 _ fcBlk_1_row_lens r hr).2
  | 2 => exact (map_len_replicate_8 _ fcBlk_2_row_lens r hr).2
  | 3 => exact (map_len_replicate_8 _ fcBlk_3_row_lens r hr).2
  | 4 => exact (map_len_replicate_8 _ fcBlk_4_row_lens r hr).2
  | 5 => exact (map_len_replicate_8 _ fcBlk_5_row_lens r hr).2
  | 6 => exact (map_len_replicate_8 _ fcBlk_6_row_lens r hr).2
  | 7 => exact (map_len_replicate_8 _ fcBlk_7_row_lens r hr).2
  | 8 => exact (map_len_replicate_8 _ fcBlk_8_row_lens r hr).2
  | 9 => exact (map_len_replicate_8 _ fcBlk_9_row_lens r hr).2
  | _ + 10 => omega

theorem rcTable_row_len (b : Nat) (hb : b < 10) :
    (rcTable[b]'(by rw [rcTable_len]; exact hb)).length = 8 := by
  match b with
  | 0 => exact rcBlk_0_len
  | 1 => exact rcBlk_1_len
  | 2 => exact rcBlk_2_len
  | 3 => exact rcBlk_3_len
  | 4 => exact rcBlk_4_len
  | 5 => exact rcBlk_5_len
  | 6 => exact rcBlk_6_len
  | 7 => exact rcBlk_7_len
  | 8 => exact rcBlk_8_len
  | 9 => exact rcBlk_9_len
  | _ + 10 => omega

theorem rcTable_cell_len (b r : Nat) (hb : b < 10) (hr : r < 8) :
    ((rcTable[b]'(by rw [rcTable_len]; exact hb))[r]'(by
      rw [rcTable_row_len b hb]; exact hr)).length = (if b < 9 then 8 else if r < 7 then 8 else 1) := by
  match b with
  | 0 => simpa [rcTable] using (map_len_replicate_8 _ rcBlk_0_row_lens r hr).2
  | 1 => simpa [rcTable] using (map_len_replicate_8 _ rcBlk_1_row_lens r hr).2
  | 2 => simpa [rcTable] using (map_len_replicate_8 _ rcBlk_2_row_lens r hr).2
  | 3 => simpa [rcTable] using (map_len_replicate_8 _ rcBlk_3_row_lens r hr).2
  | 4 => simpa [rcTable] using (map_len_replicate_8 _ rcBlk_4_row_lens r hr).2
  | 5 => simpa [rcTable] using (map_len_replicate_8 _ rcBlk_5_row_lens r hr).2
  | 6 => simpa [rcTable] using (map_len_replicate_8 _ rcBlk_6_row_lens r hr).2
  | 7 => simpa [rcTable] using (map_len_replicate_8 _ rcBlk_7_row_lens r hr).2
  | 8 => simpa [rcTable] using (map_len_replicate_8 _ rcBlk_8_row_lens r hr).2
  | 9 => simpa [rcTable] using (map_len_rcBlk_9 r hr).2
  | _ + 10 => omega

private theorem rcFlatBlocks_item_len (b : Nat) (hb : b < 10) :
    (rcFlatBlocks[b]'(by rw [rcFlatBlocks_len]; exact hb)).length = (if b < 9 then 64 else 57) := by
  match b with
  | 0 => exact rcBlk_0_flat_len
  | 1 => exact rcBlk_1_flat_len
  | 2 => exact rcBlk_2_flat_len
  | 3 => exact rcBlk_3_flat_len
  | 4 => exact rcBlk_4_flat_len
  | 5 => exact rcBlk_5_flat_len
  | 6 => exact rcBlk_6_flat_len
  | 7 => exact rcBlk_7_flat_len
  | 8 => exact rcBlk_8_flat_len
  | 9 => exact rcBlk_9_flat_len
  | _ + 10 => omega

private theorem rcFlatBlocks_eq_table_flatten (b : Nat) (hb : b < 10) :
    rcFlatBlocks[b]'(by rw [rcFlatBlocks_len]; exact hb) =
      (rcTable[b]'(by rw [rcTable_len]; exact hb)).flatten := by
  match b with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => rfl
  | _ + 10 => omega

theorem lookupFastConfRec_eq_table (h : Nat) (hh : h < 633) :
    ∃ (hb0 : h >>> 6 < Discharging.fastConfTable.length)
      (hb1 : (h >>> 3) &&& 7 < (Discharging.fastConfTable[h >>> 6]'hb0).length)
      (hb2 : h &&& 7 < ((Discharging.fastConfTable[h >>> 6]'hb0)[(h >>> 3) &&& 7]'hb1).length),
      Discharging.lookupFastConfRec h =
        ((Discharging.fastConfTable[h >>> 6]'hb0)[(h >>> 3) &&& 7]'hb1)[h &&& 7]'hb2 := by
  obtain ⟨h0, h1, h2, _, _, _⟩ := bit_chunk_arith h hh
  have hb0 : h >>> 6 < Discharging.fastConfTable.length := by rw [fastConfTable_len]; exact h0
  have hb1 : (h >>> 3) &&& 7 < (Discharging.fastConfTable[h >>> 6]'hb0).length := by
    rw [fcTable_row_len _ h0]; exact h1
  have hb2 : h &&& 7 < ((Discharging.fastConfTable[h >>> 6]'hb0)[(h >>> 3) &&& 7]'hb1).length := by
    rw [fcTable_cell_len _ _ h0 h1]; exact h2
  refine ⟨hb0, hb1, hb2, ?_⟩
  dsimp [Discharging.lookupFastConfRec]
  change lookupListRec default
      (lookupListRec [] (lookupListRec [] Discharging.fastConfTable (h >>> 6)) ((h >>> 3) &&& 7))
      (h &&& 7) = _
  rw [lookupListRec_eq_getElem _ Discharging.fastConfTable (h >>> 6) hb0]
  rw [lookupListRec_eq_getElem _ _ ((h >>> 3) &&& 7) hb1]
  rw [lookupListRec_eq_getElem _ _ (h &&& 7) hb2]

theorem parsedRConfList_eq_table (h : Nat) (hh : h < 633) :
    ∃ (hb0 : h >>> 6 < rcTable.length)
      (hb1 : (h >>> 3) &&& 7 < (rcTable[h >>> 6]'hb0).length)
      (hb2 : h &&& 7 < ((rcTable[h >>> 6]'hb0)[(h >>> 3) &&& 7]'hb1).length),
      parsedRConfList[h]'(by rw [parsedRConfList_length]; exact hh) =
        ((rcTable[h >>> 6]'hb0)[(h >>> 3) &&& 7]'hb1)[h &&& 7]'hb2 := by
  obtain ⟨h0, h1, h2, hsum1, hsum2, h9⟩ := bit_chunk_arith h hh
  have hb0 : h >>> 6 < rcTable.length := by rw [rcTable_len]; exact h0
  have hb1 : (h >>> 3) &&& 7 < (rcTable[h >>> 6]'hb0).length := by
    rw [rcTable_row_len _ h0]; exact h1
  have hb2 : h &&& 7 < ((rcTable[h >>> 6]'hb0)[(h >>> 3) &&& 7]'hb1).length := by
    rw [rcTable_cell_len _ _ h0 h1]
    by_cases hb9 : h >>> 6 < 9
    · simp [hb9, h2]
    · have hb9eq : h >>> 6 = 9 := by omega
      rcases h9 hb9eq with hlt7 | ⟨heq7, h2z⟩
      · simp [hb9, hlt7, h2]
      · simp [hb9, heq7, h2z]
  refine ⟨hb0, hb1, hb2, ?_⟩
  have hfb : h >>> 6 < rcFlatBlocks.length := by rw [rcFlatBlocks_len]; exact h0
  have hprev64 : ∀ i (hi : i < h >>> 6), (rcFlatBlocks[i]'(Nat.lt_trans hi hfb)).length = 64 := by
    intro i hi
    have hi9 : i < 9 := by omega
    rw [rcFlatBlocks_item_len i (by omega)]
    simp [hi9]
  have hmod64 : h % 64 < (rcFlatBlocks[h >>> 6]'hfb).length := by
    rw [rcFlatBlocks_item_len _ h0]
    by_cases hb9 : h >>> 6 < 9
    · simp [hb9]; exact Nat.mod_lt h (by omega)
    · have hb9eq : h >>> 6 = 9 := by omega
      simp [hb9]
      omega
  obtain ⟨hflat64, heq64⟩ := flatten_getElem_chunk 64 rcFlatBlocks (h >>> 6) (h % 64) hfb hprev64 hmod64
  have hprev8 : ∀ i (hi : i < (h >>> 3) &&& 7),
      ((rcTable[h >>> 6]'hb0)[i]'(Nat.lt_trans hi hb1)).length = 8 := by
    intro i hi
    rw [rcTable_cell_len _ i h0 (by omega)]
    by_cases hb9 : h >>> 6 < 9
    · simp [hb9]
    · have hb9eq : h >>> 6 = 9 := by omega
      rcases h9 hb9eq with hlt7 | ⟨heq7, _⟩
      · simp [hb9, show i < 7 by omega]
      · simp [hb9, show i < 7 by omega]
  obtain ⟨hflat8, heq8⟩ := flatten_getElem_chunk 8 (rcTable[h >>> 6]'hb0) ((h >>> 3) &&& 7) (h &&& 7) hb1 hprev8 hb2
  have hget_congr : ∀ (l1 l2 : List FastReducer.RConf) (hl : l1 = l2) {i j : Nat} (hij : i = j)
      (hi : i < l1.length) (hj : j < l2.length), l1[i]'hi = l2[j]'hj := by
    intro l1 l2 hl i j hij hi hj; subst hl; subst hij; rfl
  have hstep1 := hget_congr parsedRConfList rcFlatBlocks.flatten rcFlatBlocks_flatten_eq.symm hsum2.symm
    (by rw [parsedRConfList_length]; exact hh) hflat64
  have hstep2 := hget_congr (rcFlatBlocks[h >>> 6]'hfb) (rcTable[h >>> 6]'hb0).flatten
    (rcFlatBlocks_eq_table_flatten (h >>> 6) h0) hsum1.symm hmod64 hflat8
  rw [hstep1, heq64, hstep2, heq8]

end Math.Unavoidability
