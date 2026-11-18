import Lake
open Lake DSL

package "FourColorTheorem" where
  -- Cap each lean worker process to 4096 MB RAM and 1 internal thread (Lake still parallelizes across modules)
  weakLeanArgs := #["-M", "4096", "-j", "1"]

lean_lib «FourColorTheorem» where

lean_lib «Spec» where

lean_lib «Challenge» where

@[default_target]
lean_lib «Solution» where

lean_lib «SanityChecks» where

lean_lib «FiveColorTheorem» where

lean_exe "fourcolortheorem" where
  root := `Main
  moreLeancArgs := #["-O3", "-march=native", "-mtune=native"]

lean_exe "dischargetest" where
  root := `DischargeMain
  moreLeancArgs := #["-O3", "-march=native", "-mtune=native"]

lean_exe "refcheck" where
  root := `RefCheckMain
  moreLeancArgs := #["-O3", "-march=native", "-mtune=native"]
