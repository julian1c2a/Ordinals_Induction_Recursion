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

section CUB_Intersection

variable {κ : Ordinal.{u}}
variable (h_reg : IsRegular κ) (h_unc : IsUncountable κ)

noncomputable def seq_preord (C1 C2 : Ordinal.{u} → Prop) (α : Ordinal.{u})
    (h1 : IsUnbounded C1 κ) (h2 : IsUnbounded C2 κ) (hα : α < κ) (n : Nat) : UnivOrd.PreOrd.{u} :=
  Classical.choose (Quotient.exists_rep (seq C1 C2 κ α h1 h2 hα n))

noncomputable def seq_sup (C1 C2 : Ordinal.{u} → Prop) (α : Ordinal.{u})
    (h1 : IsUnbounded C1 κ) (h2 : IsUnbounded C2 κ) (hα : α < κ) : Ordinal.{u} :=
  Quotient.mk UnivOrd.PreOrd.Setoid (UnivOrd.PreOrd.sup (α := ULift.{u, 0} Nat) fun n => seq_preord C1 C2 α h1 h2 hα n.down)

/-- Dado que κ es regular y no numerable, el supremo de una sucesión ω-indexada de menores que κ es estrictamente menor que κ. -/
axiom seq_sup_lt {C1 C2 α} {h1 : IsUnbounded C1 κ} {h2 : IsUnbounded C2 κ} {hα : α < κ} :
  seq_sup C1 C2 α h1 h2 hα < κ

/-- Todo elemento de la sucesión es estrictamente menor que el supremo. -/
axiom seq_lt_sup {C1 C2 α} {h1 : IsUnbounded C1 κ} {h2 : IsUnbounded C2 κ} {hα : α < κ} (n : Nat) :
  seq C1 C2 κ α h1 h2 hα n < seq_sup C1 C2 α h1 h2 hα

/-- El supremo es un ordinal límite. -/
axiom seq_sup_is_limit {C1 C2 α} {h1 : IsUnbounded C1 κ} {h2 : IsUnbounded C2 κ} {hα : α < κ} :
  IsLimit (seq_sup C1 C2 α h1 h2 hα)

/-- C1 es no acotado por debajo de seq_sup -/
axiom seq_sup_unbounded_C1 {C1 C2 α} {h1 : IsUnbounded C1 κ} {h2 : IsUnbounded C2 κ} {hα : α < κ} :
  IsUnbounded C1 (seq_sup C1 C2 α h1 h2 hα)

/-- C2 es no acotado por debajo de seq_sup -/
axiom seq_sup_unbounded_C2 {C1 C2 α} {h1 : IsUnbounded C1 κ} {h2 : IsUnbounded C2 κ} {hα : α < κ} :
  IsUnbounded C2 (seq_sup C1 C2 α h1 h2 hα)

/-- La intersección de dos CUBs es un conjunto no acotado. -/
theorem CUB_inter_unbounded {C1 C2 : Ordinal.{u} → Prop}
    (hC1 : IsCUB C1 κ) (hC2 : IsCUB C2 κ) :
    IsUnbounded (fun α => C1 α ∧ C2 α) κ := by
  intro α hα
  let lam := seq_sup C1 C2 α hC1.right hC2.right hα
  have hlam_lt : lam < κ := seq_sup_lt
  have hlam_gt : α < lam := seq_lt_sup 0
  have h_lim : IsLimit lam := seq_sup_is_limit
  
  have hunb1 : IsUnbounded C1 lam := seq_sup_unbounded_C1
  have hunb2 : IsUnbounded C2 lam := seq_sup_unbounded_C2
  
  have h_in1 : C1 lam := hC1.left lam hlam_lt h_lim hunb1
  have h_in2 : C2 lam := hC2.left lam hlam_lt h_lim hunb2
  
  exact ⟨lam, hlam_lt, hlam_gt, h_in1, h_in2⟩

end CUB_Intersection

section CUBFilter

variable {κ : Ordinal.{u}}
variable (h_reg : IsRegular κ) (h_unc : IsUncountable κ)

/-- El filtro Club está compuesto por todos los subconjuntos que contienen un conjunto CUB. -/
def club_sets (κ : Ordinal.{u}) (X : Ordinal.{u} → Prop) : Prop :=
  ∃ C, IsCUB C κ ∧ ∀ α < κ, C α → X α

/-- El universo contiene un CUB (el propio universo) -/
axiom univ_mem_club : club_sets κ (fun α => α < κ)

/-- El conjunto vacío no contiene un CUB -/
axiom empty_not_mem_club : ¬ club_sets κ (fun _ => False)

/-- La intersección de dos conjuntos en el filtro Club está en el filtro Club -/
axiom inter_mem_club : ∀ X Y, club_sets κ X → club_sets κ Y → club_sets κ (fun α => X α ∧ Y α)

/-- Cerrado hacia arriba -/
axiom upward_closed_club : ∀ X Y, club_sets κ X → (∀ α < κ, X α → Y α) → club_sets κ Y

/-- El Filtro Club sobre un cardinal inacesible κ -/
noncomputable def CUBFilter (κ : Ordinal.{u}) (h_reg : IsRegular κ) (h_unc : IsUncountable κ) : Filter κ where
  sets := club_sets κ
  univ_mem := univ_mem_club
  empty_not_mem := empty_not_mem_club
  inter_mem := inter_mem_club
  upward_closed := upward_closed_club

end CUBFilter

end LargeCardinals
