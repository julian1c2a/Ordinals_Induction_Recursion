/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import OrdinalsInductionRecursion.UnivOrd.Ordinals
import OrdinalsInductionRecursion.UnivOrd.WellOrder

namespace UnivOrd.Ordinal

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem subset_of_mem_succ {a b : PreOrd.{u}} (h : PreOrd.Mem a (PreOrd.succ b)) : PreOrd.Subset a b := by
  cases h with
  | mem_succ hsub => exact hsub

theorem le_of_lt_succ {x y : Ordinal.{u}} (h : x < succ y) : x ≤ y := by
  revert h
  refine Quotient.inductionOn₂ x y ?_
  intro a b hab
  exact subset_of_mem_succ hab

theorem le_of_lt {x y : Ordinal.{u}} (h : x < y) : x ≤ y := by
  revert h
  refine Quotient.inductionOn₂ x y ?_
  intro a b hab
  exact PreOrd.mem_implies_subset hab

theorem le_antisymm_ord (x y : Ordinal.{u}) (h1 : x ≤ y) (h2 : y ≤ x) : x = y := by
  revert h1 h2
  refine Quotient.inductionOn₂ x y ?_
  intro a b h1 h2
  exact Quotient.sound ⟨h1, h2⟩

theorem zero_succ_limit (x : Ordinal.{u}) : x = zero ∨ (∃ y, x = succ y) ∨ IsLimit x := by
  by_cases h0 : x = zero
  · exact Or.inl h0
  · by_cases hs : ∃ y, x = succ y
    · exact Or.inr (Or.inl hs)
    · apply Or.inr; apply Or.inr
      constructor
      · exact h0
      · intro y hy
        have h_succ_le : succ y ≤ x := by
          revert hy
          refine Quotient.inductionOn₂ y x ?_
          intro a b hab
          exact PreOrd.Subset.succ_subset hab
        rcases lt_trichotomy (succ y) x with h_lt | h_eq | h_gt
        · exact h_lt
        · exfalso
          apply hs
          exact ⟨y, h_eq.symm⟩
        · have h_x_le_y : x ≤ y := le_of_lt_succ h_gt
          have h_y_le_x : y ≤ x := le_of_lt hy
          have h_eq : x = y := le_antisymm_ord x y h_x_le_y h_y_le_x
          exfalso
          subst h_eq
          exact lt_irrefl x hy

theorem lt_succ_self (x : Ordinal.{u}) : x < succ x := by
  revert x
  refine Quotient.ind ?_
  intro a
  exact PreOrd.Mem_self_succ a

/-- Principio de inducción transfinita general para Ordinales (basado en buen orden). -/
theorem inductionOn {p : Ordinal.{u} → Prop} (o : Ordinal.{u})
  (h : ∀ α, (∀ β < α, p β) → p α) : p o :=
  WellFounded.induction well_founded_lt o h

/-- Principio de inducción transfinita clasificando en cero, sucesor y límite. -/
theorem limitInductionOn {p : Ordinal.{u} → Prop} (o : Ordinal.{u})
  (hzero : p zero)
  (hsucc : ∀ α, p α → p (succ α))
  (hlimit : ∀ α, IsLimit α → (∀ β < α, p β) → p α) : p o :=
  inductionOn o fun α ih => by
    rcases zero_succ_limit α with rfl | ⟨β, rfl⟩ | hlim
    · exact hzero
    · apply hsucc
      apply ih
      exact lt_succ_self β
    · exact hlimit α hlim ih

/-- Principio de recursión transfinita sobre el buen orden. -/
def recOn {motive : Ordinal.{u} → Sort v} (o : Ordinal.{u})
  (F : ∀ α, (∀ β < α, motive β) → motive α) : motive o :=
  WellFounded.fix well_founded_lt F o

/-- Principio de recursión transfinita clasificando en cero, sucesor y límite. -/
noncomputable def limitRecOn {motive : Ordinal.{u} → Sort v} (o : Ordinal.{u})
  (hzero : motive zero)
  (hsucc : ∀ α, motive α → motive (succ α))
  (hlimit : ∀ α, IsLimit α → (∀ β < α, motive β) → motive α) : motive o :=
  recOn o fun α ih =>
    if h0 : α = zero then
      Eq.ndrec hzero h0.symm
    else if hsucc_cond : ∃ β, α = succ β then
      let β := Classical.choose hsucc_cond
      let heq := Classical.choose_spec hsucc_cond
      Eq.ndrec (hsucc β (ih β (heq ▸ lt_succ_self β))) heq.symm
    else
      let hlim : IsLimit α := by
        rcases zero_succ_limit α with rfl | ⟨β, rfl⟩ | hlim
        · exact False.elim (h0 rfl)
        · exact False.elim (hsucc_cond ⟨β, rfl⟩)
        · exact hlim
      hlimit α hlim ih

end
end UnivOrd.Ordinal
