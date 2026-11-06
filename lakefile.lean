import Lake
open Lake DSL

package "FourColorTheorem" where
  -- Hard cap each sequential lean.exe process to 4096 MB RAM and 1 thread to prevent system lag / RAM overflow
  weakLeanArgs := #["-M", "4096", "-j", "1"]

lean_lib «FourColorTheorem» where
  -- add library configuration options here

lean_lib «Spec» where

lean_lib «ConditionalBridge» where

lean_lib «ConditionalSolution» where

lean_lib «Challenge» where

lean_lib «Solution» where

lean_lib «SanityChecks» where

lean_lib «FiveColorTheorem» where

@[default_target]
lean_exe "fourcolortheorem" where
  root := `Main
  moreLeancArgs := #["-O3", "-march=native", "-mtune=native"]

lean_exe "dischargetest" where
  root := `DischargeMain
  moreLeancArgs := #["-O3", "-march=native", "-mtune=native"]
