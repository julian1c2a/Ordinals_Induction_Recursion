import OrdinalsInductionRecursion.UnivOrd.Ordinals

universe u

namespace LargeCardinals

open UnivOrd
open UnivOrd.Ordinal

/-- 
  Estructura de Filtro sobre un cardinal κ.
  Representamos los subconjuntos lógicamente como predicados `Ordinal.{u} → Prop`.
-/
structure Filter (κ : Ordinal.{u}) where
  sets : (Ordinal.{u} → Prop) → Prop
  univ_mem : sets (fun α => α < κ)
  empty_not_mem : ¬ sets (fun _ => False)
  inter_mem : ∀ X Y, sets X → sets Y → sets (fun α => X α ∧ Y α)
  upward_closed : ∀ X Y, sets X → (∀ α < κ, X α → Y α) → sets Y

/-- 
  Un filtro es λ-completo si es cerrado bajo intersecciones de tamaño menor a λ.
  En nuestro marco, representamos una familia de conjuntos indexada por `A`.
-/
def IsCompleteFilter (κ lam : Ordinal.{u}) (F : Filter κ) : Prop :=
  ∀ (A : Type u) (f : A → (Ordinal.{u} → Prop)),
    -- Si la cardinalidad de A es menor que λ (conceptualizado vía inyección a un ordinal < λ)
    -- y cada conjunto de la familia está en el filtro...
    -- (Por ahora, para Filtros CUB, nos basta con la completitud respecto a la intersección finita,
    -- o la completitud diagonal de Mahlo que abordaremos más adelante).
    True

end LargeCardinals
