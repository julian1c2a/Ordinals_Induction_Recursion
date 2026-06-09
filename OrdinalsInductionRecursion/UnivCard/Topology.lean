/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import OrdinalsInductionRecursion.UnivSets.Axioms
import OrdinalsInductionRecursion.UnivCard.Cardinal

universe u

namespace UnivCard

open UnivSets

-- ==========================================
-- Conceptos Topológicos Básicos en USet
-- ==========================================

/-- Un ordinal material L es un ordinal límite si no es vacío y no tiene máximo.
    En términos de USet, está cerrado bajo el sucesor (insert α α). -/
def IsLimitOrdinal (L : USet.{u}) : Prop :=
  L ≠ empty ∧ ∀ α ∈ L, insert α α ∈ L

/-- Un punto L ∈ USet es un punto límite topológico de una clase X si
    es un ordinal límite y todo entorno de L contiene puntos de X.
    En la topología del orden, esto significa que para todo α ∈ L,
    existe un β ∈ L mayor que α que pertenece a X. -/
def LimitPoint (X : USet.{u} → Prop) (L : USet.{u}) : Prop :=
  IsLimitOrdinal L ∧ ∀ α ∈ L, ∃ β ∈ L, α ∈ β ∧ X β

/-- Una clase X es cerrada en un cardinal κ si contiene a todos sus puntos
    límite estrictamente menores que κ. -/
def IsClosed (X : USet.{u} → Prop) (κ : USet.{u}) : Prop :=
  ∀ L ∈ κ, LimitPoint X L → X L

/-- Una clase X es no acotada (unbounded) en un cardinal κ si,
    para cualquier α ∈ κ, podemos encontrar un β ∈ κ mayor que α en X. -/
def IsUnbounded (X : USet.{u} → Prop) (κ : USet.{u}) : Prop :=
  ∀ α ∈ κ, ∃ β ∈ κ, α ∈ β ∧ X β

end UnivCard
