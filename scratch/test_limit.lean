import OrdinalsInductionRecursion.CountableOrd.Ordinals
import OrdinalsInductionRecursion.CountableOrd.ExtPreOrd

namespace CountableOrd.Ordinal

local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem subset_of_mem_succ {a b : PreOrd} (h : PreOrd.Mem a (PreOrd.succ b)) : PreOrd.Subset a b := by
  cases h with
  | mem_succ hsub => exact hsub

theorem le_of_lt_succ {x y : Ordinal} (h : x < succ y) : x ≤ y := by
  revert h
  refine Quotient.inductionOn₂ x y ?_
  intro a b hab
  exact subset_of_mem_succ hab

theorem le_of_lt {x y : Ordinal} (h : x < y) : x ≤ y := by
  revert h
  refine Quotient.inductionOn₂ x y ?_
  intro a b hab
  exact PreOrd.mem_subset hab

theorem le_antisymm_ord (x y : Ordinal) (h1 : x ≤ y) (h2 : y ≤ x) : x = y := by
  revert h1 h2
  refine Quotient.inductionOn₂ x y ?_
  intro a b h1 h2
  exact Quotient.sound ⟨h1, h2⟩

theorem mem_irrefl (a : PreOrd) : ¬ PreOrd.Mem a a := by
  intro h
  have wf : Acc PreOrd.Mem a := PreOrd.acc_mem a
  induction wf with
  | intro a' _ ih => exact ih a' h h

theorem lt_irrefl (x : Ordinal) : ¬ x < x := by
  revert x
  refine Quotient.ind ?_
  intro a ha
  exact mem_irrefl a ha

theorem zero_succ_limit2 (x : Ordinal) : x = zero ∨ (∃ y, x = succ y) ∨ IsLimit x := by
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
        -- use PreOrd.total_prop on representatives
        -- actually we can just prove lt_trichotomy here for ordinals
        have h_trichotomy : succ y < x ∨ succ y = x ∨ x < succ y := by
          revert x y
          refine Quotient.ind₂ ?_
          intro b a
          -- b is x, a is y. We want succ a < b ∨ succ a = b ∨ b < succ a
          match (PreOrd.total_prop (PreOrd.succ a) b).2.1 with
          | Or.inl hlt => exact Or.inl hlt
          | Or.inr hle =>
            match (PreOrd.total_prop (PreOrd.succ a) b).2.2 with
            | Or.inl hgt => exact Or.inr (Or.inr hgt)
            | Or.inr hge => exact Or.inr (Or.inl (Quotient.sound ⟨hle, hge⟩))
        rcases h_trichotomy with h_lt | h_eq | h_gt
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

end CountableOrd.Ordinal
