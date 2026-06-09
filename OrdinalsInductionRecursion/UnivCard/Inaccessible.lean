/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import OrdinalsInductionRecursion.UnivSets.Axioms
import OrdinalsInductionRecursion.UnivCard.Cardinal

universe u

namespace UnivCard

open UnivSets

-- ==========================================
-- Inaccesibilidad en USet
-- ==========================================

/-- Un cardinal es regular si no puede ser alcanzado por una unión de tamaño menor.
    Aquí lo expresamos de la forma: para todo α ∈ κ, y toda función f : α → κ,
    existe un β ∈ κ que acota la imagen de f. -/
def IsRegular (κ : USet.{u}) : Prop :=
  IsCardinal κ ∧
  ∀ (α : USet.{u}), α ∈ κ → ∀ (f : {a : USet.{u} // a ∈ α} → {b : USet.{u} // b ∈ κ}),
    ∃ β ∈ κ, ∀ a, (f a).val ∈ β ∨ (f a).val = β

/-- Un cardinal es límite fuerte si el tamaño del conjunto potencia de cualquier
    elemento menor es estrictamente menor que el cardinal. -/
def IsStrongLimit (κ : USet.{u}) : Prop :=
  IsCardinal κ ∧ ∀ α ∈ κ, cardSet (powerset α) ∈ κ

/-- Un ordinal es no numerable si contiene estrictamente a omega. -/
def IsUncountable (κ : USet.{u}) : Prop :=
  omega.{u} ∈ κ

/-- Un cardinal es fuertemente inaccesible si es no numerable, regular y límite fuerte. -/
def IsInaccessible (κ : USet.{u}) : Prop :=
  IsUncountable κ ∧ IsRegular κ ∧ IsStrongLimit κ

end UnivCard
