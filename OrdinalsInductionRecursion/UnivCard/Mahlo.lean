/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import OrdinalsInductionRecursion.UnivCard.Inaccessible
import OrdinalsInductionRecursion.UnivCard.CUB

universe u

namespace UnivCard

open UnivSets

-- ==========================================
-- Cardinales de Mahlo
-- ==========================================

/-- El conjunto (clase) de cardinales regulares menores que κ. -/
def RegularsBelow (κ : USet.{u}) : USet.{u} → Prop :=
  fun α => α ∈ κ ∧ IsRegular α

/-- Un cardinal κ es de Mahlo si es fuertemente inaccesible y
    el conjunto de cardinales regulares menores que κ es estacionario en κ.
    Esto implica que la propiedad de ser inaccesible "se refleja" fuertemente
    hacia abajo, asegurando que existen muchos cardinales regulares por debajo. -/
def IsMahlo (κ : USet.{u}) : Prop :=
  IsInaccessible κ ∧ IsStationary (RegularsBelow κ) κ

/-- Mahlo es mucho más fuerte que Inaccesible. Un cardinal de Mahlo
    garantiza que hay un conjunto estacionario de inaccesibles por debajo de él. -/
theorem mahlo_implies_inaccessible (κ : USet.{u}) (h : IsMahlo κ) : IsInaccessible κ :=
  h.1

end UnivCard
