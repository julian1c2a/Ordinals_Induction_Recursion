/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

-- OrdinalsInductionRecursion/VN/ActionVN.lean
--
-- Acciones de grupo: paridad con Peano `Combinatorics/GroupTheory/Action.lean`.
--
-- Estado: ✅ Stub-doc.
--   El contenido sustantivo vive en `OrdinalsInductionRecursion/Algebra/Action.lean`
--   (`HFGroupAction`, `orb`, `stab`, `orbits_partition`, `conjugAction`,
--   `mem_center_iff_conjug_fixed`). La versión abstracta sobre `HFGroup`
--   es más general que la versión concreta `FinGroup ℕ₀` de Peano.
--
-- Tabla de correspondencia:
--   Peano                                  Aczel
--   -----                                  -----
--   FinGroup G + GroupAction ψ             HFGroupAction grp X
--   GroupAction.act g x                    ψ.act g x
--   GroupAction.orb x                      ψ.orb x
--   GroupAction.stab x                     ψ.stab hx  (como HFSubgroup)
--   orb_self                               HFGroupAction.orb_self
--   orbits_partition                       HFGroupAction.orbits_partition
--   conjugAction                           HFGroupAction.conjugAction
--   center_eq_fixed                        mem_center_iff_conjug_fixed
--
-- TODO en Aczel (paridad pendiente, no bloqueante):
--   orbit_stabilizer   — vía Lagrange (CosetCount ya disponible)
--   class_equation     — corolario de orbits_partition + orbit_stabilizer

import OrdinalsInductionRecursion.Algebra.Action
import Peano.PeanoNat.Combinatorics.GroupTheory.Action

set_option autoImplicit false

namespace OrdinalsInductionRecursion
  namespace VN
    namespace Action

      /-!
      # § Paridad Action
      Ver tabla de correspondencia en la cabecera del archivo.
      El contenido sustantivo vive en `OrdinalsInductionRecursion.Algebra.Action`.
      !-/

    end Action
  end VN
end OrdinalsInductionRecursion
