/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import OrdinalsInductionRecursion.UnivCard.Structure

universe u

namespace UnivCard

open UnivSets

-- ==========================================
-- Principio de Vopěnka
-- ==========================================

/-- Una clase C de estructuras es una clase propia si sus dominios no pueden
    ser contenidos dentro de un único conjunto material S ∈ USet. -/
def IsProperClass (C : RelStructure.{u} → Prop) : Prop :=
  ∀ S : USet.{u}, ∃ A, C A ∧ ¬ (A.domain ∈ S)

/-- El Principio de Vopěnka (VP) formulado para conjuntos materiales:
    Para cualquier clase propia de estructuras relacionales (de la misma firma),
    existen dos estructuras distintas tales que hay una inmersión de la primera
    en la segunda. -/
axiom vopenka_principle (C : RelStructure.{u} → Prop) (hC : IsProperClass C) :
  ∃ A B, C A ∧ C B ∧ A ≠ B ∧ Nonempty (IsEmbedding A B)

end UnivCard
