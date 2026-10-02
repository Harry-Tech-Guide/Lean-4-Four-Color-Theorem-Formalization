import FourColorTheorem.Math.Reducibility

namespace Math

def tokenize (s : String) : List String :=
  (s.split (fun c => c.isWhitespace)).filter (fun t => t ≠ "")

def parseConfig (text : String) : Option Configuration := Id.run do
  let lines := (text.splitOn "\n").map String.trim |>.filter (fun s => s ≠ "")
  if lines.length < 3 then return none
  let header := tokenize lines[1]!
  if header.length < 2 then return none
  let totalNodes := header[0]!.toNat!
  let ringSize := header[1]!.toNat!
  
  let mut adjMatrix : Array (Array Bool) := Array.mkArray totalNodes (Array.mkArray totalNodes false)
  
  for i in [0:totalNodes] do
    if 3 + i >= lines.length then return none
    let line := tokenize lines[3 + i]!
    if line.length < 2 then return none
    let u := line[0]!.toNat! - 1
    let deg := line[1]!.toNat!
    for j in [0:deg] do
      if 2 + j < line.length then
        let v := line[2 + j]!.toNat! - 1
        if u < totalNodes && v < totalNodes then
          adjMatrix := adjMatrix.modify u (fun arr => arr.set! v true)
      
  let adjFunc := fun u v => 
    if u < totalNodes && v < totalNodes then adjMatrix[u]![v]! else false
    
  return some {
    ringSize := ringSize,
    interiorSize := totalNodes - ringSize,
    adj := adjFunc
  }

def parseAllConfigs (text : String) : Array Configuration := Id.run do
  -- Split by blank lines. A blank line is typically \n\n or \r\n\r\n.
  -- We can normalize \r\n to \n first.
  let textNorm := text.replace "\r\n" "\n"
  let blocks := textNorm.splitOn "\n\n" |>.filter (fun s => s.trim ≠ "")
  let mut configs := #[]
  for b in blocks do
    match parseConfig b with
    | some c => configs := configs.push c
    | none => continue
  return configs

end Math
