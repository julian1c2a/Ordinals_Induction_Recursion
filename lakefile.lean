import Lake
open Lake DSL

package "ordinalsinductionrecursion"

require peanolib from git
  "https://github.com/julian1c2a/Peano" @ "master"

require aczelsettheory from git
  "https://github.com/julian1c2a/AczelSetTheory.git" @ "master"

-- 🗄️ ARCHIVADO el 2026-10-28 (T50: ADR-214 y ADR-216 de ROBINSON_PlusPlus). FOL, FIJADO al último commit de
-- su `master` anterior al último de este proyecto (83a92e3, 2026-06-09): a16a111, del 2026-06-09. Antes iba por RUTA
-- (`require FOL from "../FOL"`): compilaba el árbol de trabajo de FOL de cada momento, y el de hoy ya
-- no es aquél. El registro de los consumidores de FOL: https://github.com/julian1c2a/FOL/blob/master/CONSUMIDORES.md
require «FOL» from git "https://github.com/julian1c2a/FOL" @ "a16a111ccb90945614730a0b2a3bfe28f8fe30b0"

lean_lib «OrdinalsInductionRecursion» where
  roots := #[`OrdinalsInductionRecursion]

