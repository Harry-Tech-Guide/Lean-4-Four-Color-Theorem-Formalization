import FourColorTheorem.Math.FastReducer

namespace Math
namespace FastReducer

def pow3 := powers3 15

def md6 := buildMData 6 pow3
def md7 := buildMData 7 pow3
def md8 := buildMData 8 pow3
def md9 := buildMData 9 pow3
def md10 := buildMData 10 pow3

def all_rconfs := loadAll ()

-- Ring 6
theorem c0_d_red : (check all_rconfs[0]! md6 pow3).dReducible = true := by native_decide

-- Ring 7
theorem c1_d_red : (check all_rconfs[1]! md7 pow3).dReducible = true := by native_decide

-- Ring 8
theorem c2_d_red : (check all_rconfs[2]! md8 pow3).dReducible = true := by native_decide
theorem c4_d_red : (check all_rconfs[4]! md8 pow3).dReducible = true := by native_decide
theorem c7_d_red : (check all_rconfs[7]! md8 pow3).dReducible = true := by native_decide
theorem c23_d_red : (check all_rconfs[23]! md8 pow3).dReducible = true := by native_decide

-- Ring 9
theorem c5_d_red : (check all_rconfs[5]! md9 pow3).dReducible = true := by native_decide
theorem c6_d_red : (check all_rconfs[6]! md9 pow3).dReducible = true := by native_decide
theorem c11_d_red : (check all_rconfs[11]! md9 pow3).dReducible = true := by native_decide
theorem c24_d_red : (check all_rconfs[24]! md9 pow3).dReducible = true := by native_decide
theorem c26_d_red : (check all_rconfs[26]! md9 pow3).dReducible = true := by native_decide
theorem c37_d_red : (check all_rconfs[37]! md9 pow3).dReducible = true := by native_decide
theorem c323_d_red : (check all_rconfs[323]! md9 pow3).dReducible = true := by native_decide

-- Ring 10 (sample 5 configs)
theorem c8_d_red : (check all_rconfs[8]! md10 pow3).dReducible = true := by native_decide
theorem c9_d_red : (check all_rconfs[9]! md10 pow3).dReducible = true := by native_decide
theorem c12_d_red : (check all_rconfs[12]! md10 pow3).dReducible = true := by native_decide
theorem c13_d_red : (check all_rconfs[13]! md10 pow3).dReducible = true := by native_decide
theorem c18_d_red : (check all_rconfs[18]! md10 pow3).dReducible = true := by native_decide

end FastReducer
end Math
