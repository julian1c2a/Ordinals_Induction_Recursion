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
  Un filtro es λ-completo si es cerrado bajo intersecciones de familias indexadas
  por ordinales estrictamente menores que λ.
-/
def IsCompleteFilter (κ lam : Ordinal.{u}) (F : Filter κ) : Prop :=
  ∀ (γ : Ordinal.{u}) (hγ : γ < lam) (f : Ordinal.{u} → (Ordinal.{u} → Prop)),
    (∀ α < γ, F.sets (f α)) →
    F.sets (fun β => ∀ α < γ, f α β)

/-- Un ultrafiltro es un filtro maximal: para cada conjunto, él o su complemento pertenecen al filtro. -/
def IsUltrafilter (κ : Ordinal.{u}) (F : Filter κ) : Prop :=
  ∀ X, F.sets X ∨ F.sets (fun α => ¬ X α)

/-- Un filtro es no principal si no está generado por un único elemento (no contiene singletons).
    Como los ordinales son linealmente ordenados, ser no principal es equivalente a que
    ningún conjunto acotado pertenezca al filtro (para un filtro uniforme sobre κ).
    Para medibles, formalizamos que ningún subconjunto finito pertenece. Para nuestro
    propósito, "no contiene singletons" es la base estructural. -/
def IsNonPrincipal (κ : Ordinal.{u}) (F : Filter κ) : Prop :=
  ∀ α < κ, ¬ F.sets (fun β => β = α)

end LargeCardinals
