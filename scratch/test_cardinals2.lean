import OrdinalsInductionRecursion.UnivOrd.Ordinals
import OrdinalsInductionRecursion.UnivOrd.Induction

universe u

namespace UnivOrd
namespace Cardinals

open PreOrd
open Ordinal

-- ==========================================
-- Biyecciones y Equipotencia sobre Ordinales
-- ==========================================

def Injection (α β : Ordinal.{u}) : Type (u+1) :=
  { f : {x // x < α} → {y // y < β} // Function.Injective f }

def Bijection (α β : Ordinal.{u}) : Type (u+1) :=
  { f : {x // x < α} → {y // y < β} // Function.Bijective f }

def Equipotent (α β : Ordinal.{u}) : Prop :=
  Nonempty (Bijection α β)

def IsCardinal (α : Ordinal.{u}) : Prop :=
  ∀ β < α, ¬ Equipotent α β

-- ==========================================
-- Número de Hartogs
-- ==========================================

def has_injection (α β : Ordinal.{u}) : Prop :=
  Nonempty (Injection α β)

-- El Teorema de Hartogs garantiza que para cualquier ordinal α, 
-- existe algún ordinal γ que no se puede inyectar en α.
axiom hartogs_exists (α : Ordinal.{u}) : ∃ γ, ¬ has_injection γ α

/-- El número de Hartogs de un ordinal α es el menor ordinal que no se inyecta en α. -/
def hartogs (α : Ordinal.{u}) : Ordinal.{u} :=
  WellFounded.min well_founded_lt (fun γ => ¬ has_injection γ α) (hartogs_exists α)

theorem hartogs_is_cardinal (α : Ordinal.{u}) : IsCardinal (hartogs α) := by
  sorry

-- ==========================================
-- Función Aleph
-- ==========================================

-- Necesitamos el supremo de un conjunto de ordinales para el paso límite.
-- Dado que los elementos de β son ordinales, podemos mapearlos y tomar sUnion.
def sup_over_lt (β : Ordinal.{u}) (f : (γ : Ordinal.{u}) → γ < β → Ordinal.{u}) : Ordinal.{u} :=
  -- Representamos el supremo como la unión de todos los f γ h
  -- Para construir esto formalmente requerimos mapear los elementos de un representante de β
  sorry

/-- La función Aleph que mapea cada ordinal α a su correspondiente ordinal inicial ω_α -/
def aleph (α : Ordinal.{u}) : Ordinal.{u} :=
  limitRecOn α
    omega
    (fun _ ih => hartogs ih)
    (fun β _ ih => sup_over_lt β ih)

end Cardinals
end UnivOrd
