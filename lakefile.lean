import Lake
open Lake DSL

package "ordinalsinductionrecursion"

require peanolib from git
  "https://github.com/julian1c2a/Peano" @ "master"

require aczelsettheory from git
  "https://github.com/julian1c2a/AczelSetTheory.git" @ "master"

lean_lib «OrdinalsInductionRecursion» where
  roots := #[`OrdinalsInductionRecursion]

