/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import OrdinalsInductionRecursion.UnivSets.Axioms
import OrdinalsInductionRecursion.UnivCard.Equipollence

universe u

namespace UnivCard

open UnivSets

-- ==========================================
-- Estructuras Relacionales en USet
-- ==========================================

/-- Una estructura relacional (de una sola relación binaria) sobre un conjunto material.
    Definimos la relación usando la lógica de tipos de Lean para mayor facilidad. -/
structure RelStructure where
  domain : USet.{u}
  rel : {a : USet.{u} // a ∈ domain} → {b : USet.{u} // b ∈ domain} → Prop

/-- Una inmersión estructural (embedding) entre dos estructuras relacionales A y B
    es una función inyectiva f : dom(A) → dom(B) que preserva y refleja la relación. -/
structure IsEmbedding (A B : RelStructure.{u}) where
  f : {a : USet.{u} // a ∈ A.domain} → {b : USet.{u} // b ∈ B.domain}
  injective : Function.Injective f
  preserves_rel : ∀ x y, A.rel x y ↔ B.rel (f x) (f y)

end UnivCard
