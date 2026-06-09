/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import OrdinalsInductionRecursion.UnivSets.Axioms
import OrdinalsInductionRecursion.UnivCard.Topology

universe u

namespace UnivCard

open UnivSets

-- ==========================================
-- Ultrafiltros y Cardinales Medibles
-- ==========================================

/-- Representa la existencia de la intersección material de dos conjuntos. -/
def IntersectSets (x y z : USet.{u}) : Prop :=
  ∀ a, a ∈ z ↔ a ∈ x ∧ a ∈ y

/-- F es un filtro sobre el conjunto κ. -/
def IsFilterOn (F : USet.{u} → Prop) (κ : USet.{u}) : Prop :=
  (∀ x, F x → x ∈ powerset κ) ∧
  (F κ) ∧
  (¬ F empty) ∧
  (∀ x y, F x → F y → ∀ z, IntersectSets x y z → F z) ∧
  (∀ x y, F x → x ⊆ y → y ∈ powerset κ → F y)

/-- Un filtro es principal si está generado por un único elemento α ∈ κ. -/
def IsPrincipal (F : USet.{u} → Prop) (κ : USet.{u}) : Prop :=
  ∃ α ∈ κ, ∀ x, F x ↔ (α ∈ x ∧ x ∈ powerset κ)

/-- Un ultrafiltro es un filtro maximal. Equivalentemente, para todo subconjunto,
    o bien el subconjunto o bien su complemento está en el filtro. -/
def IsUltrafilterOn (F : USet.{u} → Prop) (κ : USet.{u}) : Prop :=
  IsFilterOn F κ ∧
  ∀ x ∈ powerset κ, ∀ x_comp ∈ powerset κ,
    (∀ a, a ∈ x_comp ↔ a ∈ κ ∧ ¬ (a ∈ x)) →
    (F x ∨ F x_comp)

/-- Un filtro es κ-completo si es cerrado bajo intersecciones de tamaño < κ.
    Aquí lo formalizamos diciendo que cualquier familia de elementos del filtro,
    cuyo tamaño sea < κ (indexada por un ordinal α ∈ κ), tiene una intersección
    que también pertenece al filtro. -/
def IsKappaComplete (F : USet.{u} → Prop) (κ : USet.{u}) : Prop :=
  ∀ (α : USet.{u}), α ∈ κ →
  ∀ (f : {a : USet.{u} // a ∈ α} → {b : USet.{u} // b ∈ powerset κ}),
    (∀ a, F (f a).val) →
    ∀ z ∈ powerset κ,
      (∀ y, y ∈ z ↔ (∀ a, y ∈ (f a).val)) →
      F z

/-- Un cardinal κ es Medible si es no numerable y existe un ultrafiltro
    sobre κ que es no principal y κ-completo. -/
def IsMeasurable (κ : USet.{u}) : Prop :=
  omega.{u} ∈ κ ∧
  ∃ F, IsUltrafilterOn F κ ∧ ¬ IsPrincipal F κ ∧ IsKappaComplete F κ

end UnivCard
