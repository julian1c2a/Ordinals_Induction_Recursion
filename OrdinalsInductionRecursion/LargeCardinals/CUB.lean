import OrdinalsInductionRecursion.UnivOrd.Ordinals
import OrdinalsInductionRecursion.UnivOrd.Cardinals
import OrdinalsInductionRecursion.LargeCardinals.Inaccessible
import OrdinalsInductionRecursion.LargeCardinals.Filters

universe u

namespace LargeCardinals

open UnivOrd
open UnivOrd.Ordinal
open LargeCardinals.Inaccessible

/-- Un conjunto es no acotado en κ si siempre podemos encontrar elementos mayores. -/
def IsUnbounded (C : Ordinal.{u} → Prop) (κ : Ordinal.{u}) : Prop :=
  ∀ α < κ, ∃ β < κ, α < β ∧ C β

/-- Obtiene el siguiente elemento en un conjunto no acotado -/
noncomputable def next_C (C : Ordinal.{u} → Prop) (κ : Ordinal.{u}) (α : Ordinal.{u})
    (h : IsUnbounded C κ) (hα : α < κ) : Ordinal.{u} :=
  Classical.choose (h α hα)

theorem next_C_lt {C κ α} {h : IsUnbounded C κ} {hα : α < κ} : next_C C κ α h hα < κ :=
  (Classical.choose_spec (h α hα)).1

theorem next_C_gt {C κ α} {h : IsUnbounded C κ} {hα : α < κ} : α < next_C C κ α h hα :=
  (Classical.choose_spec (h α hα)).2.1

theorem next_C_mem {C κ α} {h : IsUnbounded C κ} {hα : α < κ} : C (next_C C κ α h hα) :=
  (Classical.choose_spec (h α hα)).2.2

/-- La sucesión alternada de elementos en C1 y C2. -/
noncomputable def seq_bounded (C1 C2 : Ordinal.{u} → Prop) (κ : Ordinal.{u}) (α : Ordinal.{u})
    (h1 : IsUnbounded C1 κ) (h2 : IsUnbounded C2 κ) (hα : α < κ) :
    Nat → { β : Ordinal.{u} // β < κ }
  | 0 => ⟨α, hα⟩
  | Nat.succ n =>
      let prev := seq_bounded C1 C2 κ α h1 h2 hα n
      if n % 2 == 0 then
        ⟨next_C C1 κ prev.val h1 prev.property, next_C_lt⟩
      else
        ⟨next_C C2 κ prev.val h2 prev.property, next_C_lt⟩

/-- La sucesión como ordinales puros. -/
noncomputable def seq (C1 C2 : Ordinal.{u} → Prop) (κ : Ordinal.{u}) (α : Ordinal.{u})
    (h1 : IsUnbounded C1 κ) (h2 : IsUnbounded C2 κ) (hα : α < κ) (n : Nat) : Ordinal.{u} :=
  (seq_bounded C1 C2 κ α h1 h2 hα n).val

/-- Un conjunto es cerrado en κ si contiene a todos sus puntos límite menores que κ. -/
def IsClosed (C : Ordinal.{u} → Prop) (κ : Ordinal.{u}) : Prop :=
  ∀ lam < κ, IsLimit lam → IsUnbounded C lam → C lam

/-- Un subconjunto CUB (Closed UnBounded). -/
def IsCUB (C : Ordinal.{u} → Prop) (κ : Ordinal.{u}) : Prop :=
  IsClosed C κ ∧ IsUnbounded C κ

/-- La intersección de dos conjuntos cerrados es cerrada. -/
theorem CUB_inter_closed {C₁ C₂ : Ordinal.{u} → Prop} {κ : Ordinal.{u}}
    (hC₁ : IsClosed C₁ κ) (hC₂ : IsClosed C₂ κ) :
    IsClosed (fun α => C₁ α ∧ C₂ α) κ := by
  intro lam hlam hlim hunb
  have hunb1 : IsUnbounded C₁ lam := by
    intro α hα
    rcases hunb α hα with ⟨β, hβ, hαβ, hC1, _⟩
    exact ⟨β, hβ, hαβ, hC1⟩
  have hunb2 : IsUnbounded C₂ lam := by
    intro α hα
    rcases hunb α hα with ⟨β, hβ, hαβ, _, hC2⟩
    exact ⟨β, hβ, hαβ, hC2⟩
  exact ⟨hC₁ lam hlam hlim hunb1, hC₂ lam hlam hlim hunb2⟩

end LargeCardinals
