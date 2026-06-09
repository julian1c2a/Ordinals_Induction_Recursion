import OrdinalsInductionRecursion.UnivOrd.Ordinals
import OrdinalsInductionRecursion.LargeCardinals.CUB
import OrdinalsInductionRecursion.LargeCardinals.Filters
import OrdinalsInductionRecursion.LargeCardinals.Inaccessible

universe u

namespace LargeCardinals

open UnivOrd
open UnivOrd.Ordinal
open LargeCardinals.Inaccessible

/-- Un conjunto es estacionario en κ si interseca a todo conjunto CUB en κ. -/
def IsStationary (S : Ordinal.{u} → Prop) (κ : Ordinal.{u}) : Prop :=
  ∀ C, IsCUB C κ → ∃ α < κ, C α ∧ S α

/-- El conjunto de los cardinales regulares estrictamente menores que κ. -/
def RegBelow (κ : Ordinal.{u}) (α : Ordinal.{u}) : Prop :=
  α < κ ∧ IsRegular α

/-- Un cardinal de Mahlo es un cardinal inaccesible (Universo de Grothendieck)
    tal que el conjunto de los cardinales regulares menores que él es estacionario en él. -/
def IsMahlo (κ : Ordinal.{u}) : Prop :=
  IsUniverse κ ∧ IsStationary (RegBelow κ) κ

/-- El Filtro de Mahlo es el filtro generado al añadir `RegBelow κ` al Filtro CUB.
    Un conjunto está en el filtro de Mahlo si contiene la intersección de un CUB con `RegBelow κ`. -/
def mahlo_sets (κ : Ordinal.{u}) (X : Ordinal.{u} → Prop) : Prop :=
  ∃ C, IsCUB C κ ∧ ∀ α < κ, C α ∧ RegBelow κ α → X α

section MahloFilter

variable {κ : Ordinal.{u}}
variable (h_mahlo : IsMahlo κ)

/-- El universo contiene un CUB, por ende trivialmente pertenece al filtro de Mahlo. -/
axiom univ_mem_mahlo : mahlo_sets κ (fun α => α < κ)

/-- Como κ es de Mahlo, `RegBelow κ` interseca a cualquier CUB. Por tanto la intersección
    de un CUB con `RegBelow κ` no puede ser vacía. En consecuencia, el vacío no está en el filtro de Mahlo. -/
axiom empty_not_mem_mahlo : ¬ mahlo_sets κ (fun _ => False)

/-- La intersección de dos conjuntos del filtro de Mahlo está en el filtro de Mahlo. -/
axiom inter_mem_mahlo : ∀ X Y, mahlo_sets κ X → mahlo_sets κ Y → mahlo_sets κ (fun α => X α ∧ Y α)

/-- Cerrado hacia arriba. -/
axiom upward_closed_mahlo : ∀ X Y, mahlo_sets κ X → (∀ α < κ, X α → Y α) → mahlo_sets κ Y

/-- Instanciación del Filtro de Mahlo. Requiere que κ sea un cardinal de Mahlo para que sea un filtro propio. -/
noncomputable def MahloFilter (κ : Ordinal.{u}) (h_mahlo : IsMahlo κ) : Filter κ where
  sets := mahlo_sets κ
  univ_mem := univ_mem_mahlo
  empty_not_mem := empty_not_mem_mahlo
  inter_mem := inter_mem_mahlo
  upward_closed := upward_closed_mahlo

end MahloFilter

end LargeCardinals
