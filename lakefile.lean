import Lake
open Lake DSL

package "FourColorTheorem" where
  -- add package configuration options here

lean_lib «FourColorTheorem» where
  -- add library configuration options here

lean_lib «FiveColorTheorem» where

@[default_target]
lean_exe "fourcolortheorem" where
  root := `Main
  moreLeancArgs := #["-O3", "-march=native", "-mtune=native"]

lean_exe "dischargetest" where
  root := `DischargeMain
  moreLeancArgs := #["-O3", "-march=native", "-mtune=native"]
