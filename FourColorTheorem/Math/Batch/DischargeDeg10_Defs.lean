import FourColorTheorem.Math.TestDischarging
import FourColorTheorem.Math.U633Parser

namespace Math.Discharging

def hs0_10 : HintStream := ([], hints_10)
def n_10_0 : ProofTree := present10 ()
def n_10_1 : ProofTree := ptLeft n_10_0
def n_10_2 : ProofTree := ptLeft n_10_1
def n_10_3 : ProofTree := ptLeft n_10_2
def n_10_4 : ProofTree := ptLeft n_10_3
def n_10_5 : ProofTree := ptRight n_10_3
def n_10_6 : ProofTree := ptRight n_10_2
def n_10_7 : ProofTree := ptRight n_10_6
def n_10_8 : ProofTree := ptLeft n_10_7
def n_10_9 : ProofTree := ptRight n_10_7
def n_10_10 : ProofTree := ptRight n_10_1
def n_10_11 : ProofTree := ptRight n_10_10
def n_10_12 : ProofTree := ptLeft n_10_11
def n_10_13 : ProofTree := ptRight n_10_11

end Math.Discharging
