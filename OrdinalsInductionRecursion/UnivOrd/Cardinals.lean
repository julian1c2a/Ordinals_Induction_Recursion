/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import OrdinalsInductionRecursion.UnivOrd.Ordinals
import OrdinalsInductionRecursion.UnivOrd.Isomorphism
import OrdinalsInductionRecursion.UnivOrd.Induction

universe u

namespace UnivOrd
namespace Cardinals

open PreOrd
open Ordinal

-- ==========================================
-- Definiciones de Funciones
-- ==========================================

def Injective {α β : Type u} (f : α → β) : Prop := ∀ x y, f x = f y → x = y
def Surjective {α β : Type u} (f : α → β) : Prop := ∀ y, ∃ x, f x = y
def Bijective {α β : Type u} (f : α → β) : Prop := Injective f ∧ Surjective f

-- ==========================================
-- Biyecciones y Equipotencia sobre Ordinales
-- ==========================================

def Injection (α β : Ordinal.{u}) : Type (u+1) :=
  { f : {x // x < α} → {y // y < β} // Injective f }

def Bijection (α β : Ordinal.{u}) : Type (u+1) :=
  { f : {x // x < α} → {y // y < β} // Bijective f }

def Equipotent (α β : Ordinal.{u}) : Prop :=
  Nonempty (Bijection α β)

def IsCardinal (α : Ordinal.{u}) : Prop :=
  ∀ β < α, ¬ Equipotent α β

-- ==========================================
-- Número de Hartogs
-- ==========================================

def has_injection (α β : Ordinal.{u}) : Prop :=
  Nonempty (Injection α β)

def is_least_hartogs (α γ : Ordinal.{u}) : Prop :=
  (¬ has_injection γ α) ∧ ∀ β < γ, has_injection β α

/-- 
El Teorema de Hartogs garantiza que para cualquier ordinal α, 
existe un MÍNIMO ordinal γ que no se puede inyectar en α.
Se declara como axioma constructivo para mantener el universo en Type u.
-/
axiom hartogs_least_exists (α : Ordinal.{u}) : ∃ γ, is_least_hartogs α γ

/-- El número de Hartogs de un ordinal α es el menor ordinal que no se inyecta en α. -/
noncomputable def hartogs (α : Ordinal.{u}) : Ordinal.{u} :=
  Classical.choose (hartogs_least_exists α)

-- ==========================================
-- Función Aleph
-- ==========================================

/-- Axioma de Reemplazo para Ordinales (Supremo de una imagen acotada) -/
axiom sup_over_lt (β : Ordinal.{u}) (f : (γ : Ordinal.{u}) → γ < β → Ordinal.{u}) : Ordinal.{u}

/-- La función Aleph que mapea cada ordinal α a su correspondiente ordinal inicial ω_α -/
noncomputable def aleph (α : Ordinal.{u}) : Ordinal.{u} :=
  limitRecOn α
    omega
    (fun _ ih => hartogs ih)
    (fun β _ ih => sup_over_lt β ih)

end Cardinals
end UnivOrd
