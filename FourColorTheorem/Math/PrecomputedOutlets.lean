module

@[expose] public section

namespace Math.Discharging

structure FastPosOut where
  isPos : Bool
  forbid : Nat
  keep : Nat
  mask : Nat
  add : Nat
  high : Nat
  deriving Repr, BEq, Inhabited

def strictNat {a : Type} (n : Nat) (k : Nat -> a) : a :=
  match n with
  | 0 => k 0
  | m + 1 => k m.succ

def all31Nat : Nat := 1155632064539505239120220611118562664264224746288220888760730478055531425056394630910709030951235393555396575
def all63Nat : Nat := 2348542582773833227889480596789337027375682548908319870707290971532209025114608443463698998384768703031934975
def emptyImgNat : Nat := 1532495540865888858358347027150309183618739122183602175

def getLaneNat (st : Nat) (p : Nat) : Nat :=
  Nat.land (Nat.shiftRight st (Nat.mul p 6)) 63

def setLaneNat (st : Nat) (p : Nat) (val : Nat) : Nat :=
  let sh := Nat.mul p 6
  let clear := Nat.xor all63Nat (Nat.shiftLeft 63 sh)
  Nat.lor (Nat.land st clear) (Nat.shiftLeft (Nat.land val 63) sh)

def getImgNat (im : Nat) (u : Nat) : Nat :=
  Nat.land (Nat.shiftRight im (Nat.mul u 6)) 63

def setImgNat (im : Nat) (u : Nat) (val : Nat) : Nat :=
  let sh := Nat.mul u 6
  let clear := Nat.xor emptyImgNat (Nat.shiftLeft 63 sh)
  Nat.lor (Nat.land im clear) (Nat.shiftLeft (Nat.land val 63) sh)

def condMaskNat (m : Int) : Nat :=
  if m > 0 then
    let mn := m.toNat
    if mn <= 5 then 31
    else if mn == 6 then 30
    else if mn == 7 then 28
    else if mn == 8 then 24
    else 16
  else
    let um := (-m).toNat
    if um == 5 then 1
    else if um == 6 then 3
    else if um == 7 then 7
    else if um == 8 then 15
    else 31

def outletForcedSWAR (st : Nat) (po : FastPosOut) : Bool :=
  Nat.beq (Nat.land st po.forbid) 0

def outletPermittedSWAR (st : Nat) (po : FastPosOut) : Bool :=
  Nat.beq (Nat.land (Nat.add (Nat.land st po.mask) po.add) po.high) po.high

def narrowSWAR (st : Nat) (po : FastPosOut) : Nat :=
  Nat.land st po.keep

end Math.Discharging
