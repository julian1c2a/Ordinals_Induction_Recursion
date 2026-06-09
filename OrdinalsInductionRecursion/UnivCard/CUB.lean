/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import OrdinalsInductionRecursion.UnivCard.Topology

universe u

namespace UnivCard

open UnivSets

-- ==========================================
-- Conjuntos Cerrados y No Acotados (CUB) en USet
-- ==========================================

/-- Un conjunto (clase) C es CUB en un cardinal κ si es cerrado y no acotado en κ. -/
def IsCUB (C : USet.{u} → Prop) (κ : USet.{u}) : Prop :=
  IsClosed C κ ∧ IsUnbounded C κ

/-- Un conjunto S es estacionario en κ si tiene intersección no vacía
    con cualquier conjunto CUB en κ. -/
def IsStationary (S : USet.{u} → Prop) (κ : USet.{u}) : Prop :=
  ∀ C, IsCUB C κ → ∃ α ∈ κ, S α ∧ C α

-- Nota: Para que la teoría CUB sea útil, κ debe ser de cofinalidad no numerable.
-- Los conjuntos CUB forman un filtro (el filtro CUB) sobre κ.

/-- La intersección de dos conjuntos es la conjunción lógica en el contexto de predicados. -/
def Intersect (C D : USet.{u} → Prop) : USet.{u} → Prop :=
  fun α => C α ∧ D α

theorem IsClosed_intersect {C D : USet.{u} → Prop} {κ : USet.{u}}
    (hc : IsClosed C κ) (hd : IsClosed D κ) : IsClosed (Intersect C D) κ := by
  intro L hL h_lim
  have h_lim_C : LimitPoint C L := by
    rcases h_lim with ⟨h_lim_ord, h_unb⟩
    constructor
    · exact h_lim_ord
    · intro α hα
      rcases h_unb α hα with ⟨β, hβ_in_L, hα_in_β, hXβ⟩
      exact ⟨β, hβ_in_L, hα_in_β, hXβ.1⟩
  have h_lim_D : LimitPoint D L := by
    rcases h_lim with ⟨h_lim_ord, h_unb⟩
    constructor
    · exact h_lim_ord
    · intro α hα
      rcases h_unb α hα with ⟨β, hβ_in_L, hα_in_β, hXβ⟩
      exact ⟨β, hβ_in_L, hα_in_β, hXβ.2⟩
  exact ⟨hc L hL h_lim_C, hd L hL h_lim_D⟩

end UnivCard
