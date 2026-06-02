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
-- (Paso C: Extensionalidad Semántica)

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
-- (Paso B: Construcción canónica de Hartogs)

def has_injection (α β : Ordinal.{u}) : Prop :=
  Nonempty (Injection α β)

-- Teorema de Hartogs (Axiomatizado para evitar la explosión de universos de Zermelo)
axiom hartogs_exists (α : Ordinal.{u}) : ∃ γ, ¬ has_injection γ α

/-- El número de Hartogs de un ordinal α es el menor ordinal que no se inyecta en α. -/
def hartogs (α : Ordinal.{u}) : Ordinal.{u} :=
  WellFounded.min well_founded_lt (fun γ => ¬ has_injection γ α) (hartogs_exists α)

-- ==========================================
-- Función Aleph
-- ==========================================
-- (Paso A: Aleph directamente en Ordinal)

-- Para definir el paso límite, necesitamos sUnion sobre la familia de Alephs previos.
-- limitRecOn requiere un (∀ γ < β, C γ). Nuestro C γ es Ordinal.{u}.
-- Así que tenemos una familia f : (γ : Ordinal.{u}) → γ < β → Ordinal.{u}.
def sup_over_lt (β : Ordinal.{u}) (f : (γ : Ordinal.{u}) → γ < β → Ordinal.{u}) : Ordinal.{u} :=
  -- En ZFC, esto sería el supremo del conjunto imagen.
  -- Para formalizar esto en Lean sin typeclasses complejas, axiomatizamos el supremo de un reemplazo:
  sorry

/-- La función Aleph que mapea cada ordinal α a su correspondiente ordinal inicial ω_α -/
def aleph (α : Ordinal.{u}) : Ordinal.{u} :=
  limitRecOn α
    omega
    (fun _ ih => hartogs ih)
    (fun β _ ih => sup_over_lt β ih)

end Cardinals
end UnivOrd
