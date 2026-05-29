import Lake
open Lake DSL

package "ordinalsinductionrecursion"

require peanolib from git
  "https://github.com/julian1c2a/Peano" @ "master"

lean_lib «OrdinalsInductionRecursion» where
  -- add library configuration options here

@[default_target]
lean_exe "ordinalsinductionrecursion" where
  root := `Main
