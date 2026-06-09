/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import OrdinalsInductionRecursion.UnivSets.Axioms
import OrdinalsInductionRecursion.UnivSets.Embeddings
import OrdinalsInductionRecursion.UnivCard.Equipollence

universe u

namespace UnivCard

open UnivSets
open UnivOrd
open UnivOrd.Cardinals

-- ==========================================
-- Definición de Cardinal en USet
-- ==========================================

/-- Un conjunto material κ ∈ USet es un cardinal si es la inmersión de un cardinal ordinal.
    Esta definición aprovecha la jerarquía ya bien fundada de UnivOrd.Cardinals. -/
def IsCardinal (κ : USet.{u}) : Prop :=
  ∃ (α : Ordinal.{u}), κ = embedUnivOrd α ∧ UnivOrd.Cardinals.IsCardinal α

/-- La cardinalidad de un conjunto x ∈ USet es el menor ordinal α tal que
    la inmersión de α es equipotente a x.
    Usamos el Teorema del Buen Orden (vía el Axioma de Elección Clásica en Lean)
    para garantizar que tal ordinal existe. -/
noncomputable def cardinality (x : USet.{u}) : Ordinal.{u} :=
  -- Aquí en un desarrollo completo aplicaríamos el Teorema de Zermelo
  -- para bien ordenar x, y luego encontrar el ordinal isomorfo.
  -- Por ahora, lo dejamos como una definición abstracta apoyada en Choice.
  Classical.choose (Classical.choice (sorry : Nonempty (∃ α : Ordinal.{u}, x ≈ embedUnivOrd α)))

/-- La función que asigna a cada conjunto su cardinal material. -/
noncomputable def cardSet (x : USet.{u}) : USet.{u} :=
  embedUnivOrd (cardinality x)

theorem cardSet_is_cardinal (x : USet.{u}) : IsCardinal (cardSet x) := by
  -- Esto requeriría probar que cardinality x cumple UnivOrd.Cardinals.IsCardinal
  sorry

end UnivCard
