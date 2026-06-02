import OrdinalsInductionRecursion.UnivOrd.Ordinals
import OrdinalsInductionRecursion.UnivOrd.Cardinals
import OrdinalsInductionRecursion.UnivOrd.Induction

universe u

namespace UnivOrd
namespace Inaccessible

open Ordinal
open Cardinals

/-- Un ordinal es regular si no puede ser alcanzado por un supremo de tamaño menor. -/
def IsRegular (α : Ordinal.{u}) : Prop :=
  IsCardinal α ∧
  ∀ (β : Ordinal.{u}) (_hβ : β < α) (f : (γ : Ordinal.{u}) → γ < β → Ordinal.{u}),
    (∀ γ hγ, f γ hγ < α) → sup_over_lt β f < α

/-- Postulamos la existencia del cardinal del conjunto potencia para evaluar límites fuertes. -/
axiom power_cardinal (α : Ordinal.{u}) : Ordinal.{u}

/-- Un cardinal límite fuerte es aquel cerrado bajo el conjunto potencia. -/
def IsStrongLimit (α : Ordinal.{u}) : Prop :=
  IsCardinal α ∧ ∀ β < α, power_cardinal β < α

/-- Un ordinal es no numerable si es estrictamente mayor que ω. -/
def IsUncountable (α : Ordinal.{u}) : Prop :=
  omega < α

/-- Un Universo (en el sentido de Grothendieck/inaccesible) es un cardinal regular, límite fuerte y no numerable. -/
def IsUniverse (α : Ordinal.{u}) : Prop :=
  IsRegular α ∧ IsStrongLimit α ∧ IsUncountable α

/-- Axioma de Universos de Grothendieck: Para todo ordinal existe un universo que lo contiene. -/
axiom grothendieck_universes (α : Ordinal.{u}) : ∃ U, α < U ∧ IsUniverse U

/-- Obtiene el siguiente universo a partir de un ordinal dado. -/
noncomputable def nextUniverse (α : Ordinal.{u}) : Ordinal.{u} :=
  Classical.choose (grothendieck_universes α)

/-- La jerarquía de universos iterada transfinitamente (Ω_α). -/
noncomputable def omega_hierarchy (α : Ordinal.{u}) : Ordinal.{u} :=
  limitRecOn α
    (nextUniverse zero)
    (fun _ ih => nextUniverse ih)
    (fun β _ ih => nextUniverse (sup_over_lt β ih))

end Inaccessible
end UnivOrd
