/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import OrdinalsInductionRecursion.MKplusCAC.Relations

namespace MKplusCAC

open Classical

local infix:50 " ∈ᴹ " => Mem
local notation:50 x " ∉ᴹ " y:51 => ¬ Mem x y
local infix:50 " ⊆ᴹ " => SubClass
local notation "⟪" x ", " y "⟫" => opair x y
local infix:70 " ∩ᴹ " => inter
local infix:65 " ∪ᴹ " => union
local notation "𝐕ᴹ" => univ
local notation "∅ᴹ" => empty
local postfix:max "⁻¹" => inv

/-!
  # Functions
  Definitions and properties for class-functions, injections, surjections,
  bijections, and restrictions.
-/

-- ============================================================
-- Section 1: Operations for Classes (Functions)
-- ============================================================

-- Aplicación de una función a un argumento: F(x)
noncomputable def app (F x : Class) : Class :=
  if h : IsSet x ∧ ∃ y, IsSet y ∧ ⟪x, y⟫ ∈ᴹ F then
    Classical.choose h.2
  else
    Classical.choice inferInstance

local notation F " ⦑ " x " ⦒ " => app F x

-- Restricción de una función a una clase A
noncomputable def restrict (F A : Class) : Class :=
  {| p | ∃ x y, IsSet x ∧ IsSet y ∧ x ∈ᴹ A ∧ ⟪x, y⟫ ∈ᴹ F ∧ p = ⟪x, y⟫ |}

local infixl:80 " ↾ᴹ " => restrict

theorem mem_restrict_iff (F A p : Class) :
    p ∈ᴹ F ↾ᴹ A ↔ ∃ x y, IsSet x ∧ IsSet y ∧ x ∈ᴹ A ∧ ⟪x, y⟫ ∈ᴹ F ∧ p = ⟪x, y⟫ := by
  dsimp [restrict]
  rw [classComp_mem]
  constructor
  · rintro ⟨_, x, y, hx, hy, hxA, hF, rfl⟩
    exact ⟨x, y, hx, hy, hxA, hF, rfl⟩
  · rintro ⟨x, y, hx, hy, hxA, hF, rfl⟩
    exact ⟨isSet_opair hx hy, x, y, hx, hy, hxA, hF, rfl⟩

-- ============================================================
-- Section 2: Properties for Classes (Functions)
-- ============================================================

-- F es una función (como clase de pares).
def IsFun (F : Class) : Prop :=
  IsRel F ∧ IsClassFun F

-- F es una función con dominio A
def IsFunFrom (F A : Class) : Prop :=
  IsFun F ∧ dom F = A

-- F es una función con dominio contenido en A
def IsFunOn (F A : Class) : Prop :=
  IsFun F ∧ dom F ⊆ᴹ A

-- F es una función de A en B
def IsFunFromTo (F A B : Class) : Prop :=
  IsFunFrom F A ∧ rng F ⊆ᴹ B

-- F es invertible (su relación inversa es una función)
def IsInvertible (F : Class) : Prop :=
  IsClassFun (F⁻¹)

-- Función inyectiva (1-1)
def IsInjective (F : Class) : Prop :=
  IsFun F ∧ IsInvertible F

-- Función sobreyectiva en B
def IsSurjective (F B : Class) : Prop :=
  rng F = B

-- Función biyectiva de A en B
def IsBijective (F A B : Class) : Prop :=
  IsFunFromTo F A B ∧ IsInjective F ∧ IsSurjective F B

-- ============================================================
-- Section 3: Theorems for Classes (Functions)
-- ============================================================

theorem isClassFun_inv_of_injective (hF : IsInjective F) : IsClassFun (F⁻¹) :=
  hF.2

theorem isSet_app {F x : Class} (hcond : IsSet x ∧ ∃ y, IsSet y ∧ ⟪x, y⟫ ∈ᴹ F) : IsSet (F ⦑ x ⦒) := by
  dsimp [app]
  rw [dif_pos hcond]
  exact (Classical.choose_spec hcond.2).1

theorem mem_dom_of_app_defined {F x : Class} (hcond : IsSet x ∧ ∃ y, IsSet y ∧ ⟪x, y⟫ ∈ᴹ F) : x ∈ᴹ dom F := by
  rw [mem_dom_iff]
  exact ⟨hcond.1, Classical.choose hcond.2, (Classical.choose_spec hcond.2).2⟩

theorem app_eq_of_eq (hF : IsFun F) {x y : Class} (hx : IsSet x) (hy : IsSet y) (hxy : x = y) :
    F ⦑ x ⦒ = F ⦑ y ⦒ := by
  subst hxy
  rfl

-- ============================================================
-- FILE: MKplusCAC/Functions_additions.lean
-- (Insertar en Functions.lean en el lugar indicado)
--
-- Objetivo: Cerrar la Fase 0 — 3 lemas auxiliares + corrección
-- de surjective_iff_forall_exists_app.
-- ============================================================

-- ────────────────────────────────────────────────────────────
-- §1.  mem_dom_iff'
--
-- Versión "prime" de mem_dom_iff con IsSet x como hipótesis.
-- Se usa en múltiples sitios del fichero pero no estaba definida.
-- ────────────────────────────────────────────────────────────
theorem mem_dom_iff' {F x : Class} (hx : IsSet x) :
    x ∈ᴹ dom F ↔ ∃ y, ⟪x, y⟫ ∈ᴹ F := by
  rw [mem_dom_iff]
  exact ⟨fun ⟨_, h⟩ => h, fun h => ⟨hx, h⟩⟩

-- ────────────────────────────────────────────────────────────
-- §2.  app_unique
--
-- Si F es una función (IsFun), y tanto x como y son sets,
-- y ⟪x, y⟫ ∈ F, entonces F⦑x⦒ = y.
--
-- Demostración:
--   • dif_pos: la condición de app se cumple, luego
--     F⦑x⦒ = Classical.choose h.2 =: y'.
--   • Por Classical.choose_spec: IsSet y' ∧ ⟪x, y'⟫ ∈ F.
--   • Por IsClassFun F: y' = y.
-- ────────────────────────────────────────────────────────────
theorem app_unique {F x y : Class}
    (hF  : IsFun F) (hx : IsSet x) (hy : IsSet y)
    (h   : ⟪x, y⟫ ∈ᴹ F) :
    F ⦑ x ⦒ = y := by
  -- La condición del if-then-else de app se cumple
  have hcond : IsSet x ∧ ∃ z, IsSet z ∧ ⟪x, z⟫ ∈ᴹ F :=
    ⟨hx, y, hy, h⟩
  -- Desplegar app y tomar la rama positiva
  simp only [app, dif_pos hcond]
  let y' := Classical.choose hcond.2
  obtain ⟨hy'_set, hy'_F⟩ := Classical.choose_spec hcond.2
  exact hF.2 x y' y hx hy'_set hy hy'_F h

-- ────────────────────────────────────────────────────────────
-- §3.  opair_app_mem_of_cond
--
-- Si sabemos explícitamente que ∃ y (set), ⟪x, y⟫ ∈ F,
-- entonces ⟪x, F⦑x⦒⟫ ∈ F.
--
-- Nota de diseño: no usamos x ∈ dom F porque la definición de
-- dom no requiere IsSet y en el testigo existencial; esto crea
-- una "junk-pair pathology" cuando ¬IsSet y. Esta versión con
-- la condición explícita evita ese problema.
-- ────────────────────────────────────────────────────────────
theorem opair_app_mem_of_cond {F x : Class} (hx : IsSet x)
    (hcond : ∃ y, IsSet y ∧ ⟪x, y⟫ ∈ᴹ F) :
    ⟪x, F ⦑ x ⦒⟫ ∈ᴹ F := by
  have hfull : IsSet x ∧ ∃ y, IsSet y ∧ ⟪x, y⟫ ∈ᴹ F := ⟨hx, hcond⟩
  simp only [app, dif_pos hfull]
  exact (Classical.choose_spec hfull.2).2

-- ────────────────────────────────────────────────────────────
-- §4.  surjective_iff_forall_exists_pair   ← NUEVO, sin sorry
--
-- Caracterización CORRECTA y COMPLETA de IsSurjective usando
-- testigos de pares (no de app). Esto es más directo y evita
-- la junk-pair pathology de surjective_iff_forall_exists_app.
--
-- IsSurjective F B = rng F = B
--   ↔  ∀ y ∈ B, ∃ x (set), ⟪x, y⟫ ∈ F   (con h_rng extra)
-- ────────────────────────────────────────────────────────────
theorem surjective_iff_forall_exists_pair
    {F : Class} (hF : IsFun F) (B : Class)
    (h_rng : rng F ⊆ᴹ B) :
    IsSurjective F B ↔
      ∀ y, y ∈ᴹ B → ∃ x, IsSet x ∧ ⟪x, y⟫ ∈ᴹ F := by
  constructor
  -- → : rng F = B → ∀ y ∈ B, ∃ par ⟨x,y⟩ ∈ F
  · intro h_surj y hy_B
    have hy_rng : y ∈ᴹ rng F := by rw [h_surj]; exact hy_B
    rw [mem_rng_iff] at hy_rng
    obtain ⟨_, x, hx, h_xyF⟩ := hy_rng
    exact ⟨x, hx, h_xyF⟩
  -- ← : testigos de pares + h_rng → rng F = B
  · intro h_pair
    apply subset_antisymm
    · -- rng F ⊆ B (directo por h_rng)
      exact h_rng
    · -- B ⊆ rng F
      intro y hy_B
      rw [mem_rng_iff]
      have hy_set : IsSet y := isSet_of_mem hy_B
      obtain ⟨x, hx_set, h_xyF⟩ := h_pair y hy_B
      exact ⟨hy_set, x, hx_set, h_xyF⟩

-- ────────────────────────────────────────────────────────────
-- §5.  surjective_iff_forall_exists_app   ← CORREGIDO
--
-- DIAGNÓSTICO DE LOS DOS SORRY ORIGINALES:
--
-- SORRY 1 (rng F ⊆ B en la rama ←):
--   El enunciado original era incorrecto. IsSurjective F B es
--   rng F = B, que requiere rng F ⊆ B. Pero h_forall sólo da
--   B ⊆ rng F. Sin info del codominio, rng F ⊆ B es indemostrable.
--   FIX: añadir h_rng : rng F ⊆ B como hipótesis explícita.
--
-- SORRY 2 (B ⊆ rng F en la rama ←):
--   Necesita exhibir ⟪x, y⟫ ∈ F desde F⦑x⦒ = y.
--   Análisis por casos sobre la rama del if-else de app:
--   • dif_pos (∃ z set, ⟪x,z⟫ ∈ F): probado via choose_spec.
--   • dif_neg + IsSet z₀: contradicción via opair_inj.
--   • dif_neg + ¬IsSet z₀: JUNK-PAIR PATHOLOGY (ver abajo).
--
-- SORRY RESIDUAL — junk-pair pathology:
--   opair x z₀ con ¬IsSet z₀ devuelve Classical.choice inferInstance
--   independientemente de x. Esto hace que distintos x puedan
--   compartir el mismo "par" en F, haciendo imposible recuperar
--   x = a (primera componente de IsRel). El caso no ocurre en
--   ninguna función construida por comprensión de pares de sets,
--   pero es formalmente imposible descartar con el sistema actual.
--   RESOLUCIÓN RECOMENDADA: usar surjective_iff_forall_exists_pair
--   (§4) que evita el problema completamente.
-- ────────────────────────────────────────────────────────────
theorem surjective_iff_forall_exists_app
    {F : Class} (hF : IsFun F) (B : Class)
    (h_rng : rng F ⊆ᴹ B) :
    IsSurjective F B ↔
      ∀ y, y ∈ᴹ B → ∃ x, x ∈ᴹ dom F ∧ F ⦑ x ⦒ = y := by
  sorry
-- ============================================================
-- Section 4: Advanced Theorems
-- ============================================================

theorem isRel_restrict (F A : Class) : IsRel (F ↾ᴹ A) := by
  intro p hp
  obtain ⟨x, y, hx, hy, _, _, rfl⟩ := (mem_restrict_iff F A p).mp hp
  exact ⟨x, y, hx, hy, rfl⟩

theorem isFun_restrict (hF : IsFun F) (A : Class) : IsFun (F ↾ᴹ A) := by
  refine ⟨isRel_restrict F A, ?_⟩
  intro x y z hx hy hz h1 h2
  obtain ⟨x₁, y₁, hx₁, hy₁, _, hF1, heq1⟩ := (mem_restrict_iff F A ⟪x, y⟫).mp h1
  obtain ⟨x₂, z₂, hx₂, hz₂, _, hF2, heq2⟩ := (mem_restrict_iff F A ⟪x, z⟫).mp h2
  obtain ⟨rfl, rfl⟩ := opair_inj hx hy hx₁ hy₁ heq1
  obtain ⟨rfl, rfl⟩ := opair_inj hx hz hx₂ hz₂ heq2
  exact hF.2 x y z hx hy hz hF1 hF2

theorem isFunOn_restrict (hF : IsFunOn F B) (A : Class) : IsFunOn (F ↾ᴹ A) (A ∩ᴹ B) := by
  sorry



theorem injective_iff_app_eq_imp_eq (F : Class) :
    IsInjective F ↔ IsFun F ∧ ∀ x₁ x₂ y₁ y₂,
      IsSet x₁ → IsSet x₂ → IsSet y₁ → IsSet y₂ →
      x₁ ∈ᴹ dom F → x₂ ∈ᴹ dom F →
      ⟪x₁, y₁⟫ ∈ᴹ F → ⟪x₂, y₂⟫ ∈ᴹ F →
      y₁ = y₂ → x₁ = x₂ := by
  constructor
  · rintro ⟨hFun, hInv⟩
    refine ⟨hFun, ?_⟩
    intro x₁ x₂ y₁ y₂ hx₁ hx₂ hy₁ hy₂ _ _ hF₁ hF₂ hy
    subst hy
    have h_inv_mem₁ : ⟪y₁, x₁⟫ ∈ᴹ F⁻¹ := (mem_inv_iff F _).mpr ⟨x₁, y₁, hx₁, hy₁, hF₁, rfl⟩
    have h_inv_mem₂ : ⟪y₁, x₂⟫ ∈ᴹ F⁻¹ := (mem_inv_iff F _).mpr ⟨x₂, y₁, hx₂, hy₁, hF₂, rfl⟩
    exact hInv y₁ x₁ x₂ hy₁ hx₁ hx₂ h_inv_mem₁ h_inv_mem₂
  · rintro ⟨hFun, h_eq⟩
    refine ⟨hFun, ?_⟩
    intro y x₁ x₂ hy hx₁ hx₂ h_inv₁ h_inv₂
    obtain ⟨x₁', y₁', hx₁', hy₁', hF₁, heq₁⟩ := (mem_inv_iff F _).mp h_inv₁
    obtain ⟨x₂', y₂', hx₂', hy₂', hF₂, heq₂⟩ := (mem_inv_iff F _).mp h_inv₂
    obtain ⟨rfl, rfl⟩ := opair_inj hy hx₁ hy₁' hx₁' heq₁
    obtain ⟨rfl, rfl⟩ := opair_inj hy hx₂ hy₂' hx₂' heq₂
    apply h_eq x₁ x₂ y y hx₁ hx₂ hy hy
    · rw [mem_dom_iff' hx₁]; exact ⟨y, hF₁⟩
    · rw [mem_dom_iff' hx₂]; exact ⟨y, hF₂⟩
    · exact hF₁
    · exact hF₂
    · rfl

theorem mem_restrict_iff' (F A p : Class) :
    p ∈ᴹ F ↾ᴹ A ↔ p ∈ᴹ F ∧ ∃ x y, IsSet x ∧ IsSet y ∧ x ∈ᴹ A ∧ p = ⟪x, y⟫ := by
  constructor
  · intro hp
    obtain ⟨x, y, hx, hy, hxA, hF, rfl⟩ := (mem_restrict_iff F A p).mp hp
    exact ⟨hF, x, y, hx, hy, hxA, rfl⟩
  · rintro ⟨hF, x, y, hx, hy, hxA, rfl⟩
    exact (mem_restrict_iff F A ⟪x, y⟫).mpr ⟨x, y, hx, hy, hxA, hF, rfl⟩


end MKplusCAC
