import FourColorTheorem
import FourColorTheorem.Math.Checker
import FourColorTheorem.Math.Parser

open Math

def main : IO Unit := do
  IO.println s!"Four Color Theorem Project Initialized!"
  
  let path := "4ct-main/configurations/U_633.conf"
  IO.println s!"Loading configurations from {path}..."
  let content ← IO.FS.readFile path
  
  let configs := parseAllConfigs content
  IO.println s!"Parsed {configs.size} configurations!"
  
  if configs.size > 0 then
    let c0 := configs[0]!
    IO.println s!"Configuration 0: ringSize={c0.ringSize}, interiorSize={c0.interiorSize}, totalNodes={c0.totalNodes}"
    
    IO.println s!"Running native Lean D-Reducibility checker on Configuration 0 (Birkhoff Diamond)..."
    let res0 := checkDReducible c0
    IO.println s!"Is Configuration 0 D-Reducible? {res0}"
    
    if configs.size > 1 then
      let c1 := configs[1]!
      IO.println s!"\nConfiguration 1: ringSize={c1.ringSize}, interiorSize={c1.interiorSize}"
      let res1 := checkDReducible c1
      IO.println s!"Is Configuration 1 D-Reducible? {res1}"

