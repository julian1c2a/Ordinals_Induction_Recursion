import OrdinalsInductionRecursion.CountableSets.HCSet

open Peano

namespace CountableSets

open Tree

-- ══════════════════════════════════════════════════════════════════
-- § 1. Conjunto Vacío
-- ══════════════════════════════════════════════════════════════════

def empty : HCSet := Quotient.mk CountableSets.Setoid .zero

theorem not_mem_empty (x : HCSet) : ¬ (x ∈ empty) := by
  induction x using Quotient.ind
  rename_i a
  intro h
  change HCSet.Mem _ _ at h
  -- h : HCSet.Mem (Quotient.mk Setoid a) empty
  -- HCSet.Mem (mk a) (mk zero) = Mem a zero
  -- which is empty
  have h' : CountableSets.Mem a .zero := h
  cases h'

-- ══════════════════════════════════════════════════════════════════
-- § 2. Adjunción (Inserción de un elemento)
-- ══════════════════════════════════════════════════════════════════

def insertTree (a b : Tree) : Tree :=
  match b with
  | .zero => .succ a
  | .succ c => .sup fun n => match n with
    | Peano.ℕ₀.zero => a
    | Peano.ℕ₀.succ _ => c
  | .sup f => .sup fun n => match n with
    | Peano.ℕ₀.zero => a
    | Peano.ℕ₀.succ n => f n

theorem mem_insertTree_self (a b : Tree) : Mem a (insertTree a b) := by
  unfold insertTree
  split
  · exact .mem_succ (Subset_refl a) (Subset_refl a)
  · rename_i c
    exact .mem_sup Peano.ℕ₀.zero (Subset_refl a) (Subset_refl a)
  · rename_i f
    exact .mem_sup Peano.ℕ₀.zero (Subset_refl a) (Subset_refl a)

theorem mem_insertTree_of_mem {x a b : Tree} (h : Mem x b) : Mem x (insertTree a b) := by
  unfold insertTree
  split
  · cases h
  · rename_i c
    cases h
    rename_i hx_c hc_x
    exact .mem_sup (Peano.ℕ₀.succ Peano.ℕ₀.zero) hx_c hc_x
  · rename_i f
    cases h
    rename_i n hx_fn hfn_x
    exact .mem_sup (Peano.ℕ₀.succ n) hx_fn hfn_x

theorem mem_of_mem_insertTree {x a b : Tree} (h : Mem x (insertTree a b)) : Equiv x a ∨ Mem x b := by
  unfold insertTree at h
  split at h
  · cases h
    rename_i hx_a ha_x
    exact Or.inl ⟨hx_a, ha_x⟩
  · rename_i c
    cases h
    rename_i n hx h_x
    cases n
    · exact Or.inl ⟨hx, h_x⟩
    · exact Or.inr (.mem_succ hx h_x)
  · rename_i f
    cases h
    rename_i n hx h_x
    cases n
    · exact Or.inl ⟨hx, h_x⟩
    · exact Or.inr (.mem_sup _ hx h_x)

theorem subset_def {a b : Tree} : Subset a b ↔ ∀ x, Mem x a → Mem x b := by
  constructor
  · intro h x hx
    exact Mem_Subset_trans hx h
  · intro h
    match a with
    | .zero => exact .zero_subset b
    | .succ c =>
      have hc : Mem c (.succ c) := .mem_succ (Subset_refl c) (Subset_refl c)
      have hc' := h c hc
      exact .succ_subset hc'
    | .sup f =>
      apply Subset.sup_subset
      intro n
      have hf : Mem (f n) (.sup f) := .mem_sup n (Subset_refl (f n)) (Subset_refl (f n))
      exact h (f n) hf

theorem equiv_def {a b : Tree} : Equiv a b ↔ ∀ x, Mem x a ↔ Mem x b := by
  constructor
  · intro h x
    constructor
    · intro hx; exact Mem_Subset_trans hx h.left
    · intro hx; exact Mem_Subset_trans hx h.right
  · intro h
    constructor
    · apply subset_def.mpr; intro x hx; exact (h x).mp hx
    · apply subset_def.mpr; intro x hx; exact (h x).mpr hx

theorem insertTree_respects {a₁ a₂ b₁ b₂ : Tree} (ha : Equiv a₁ a₂) (hb : Equiv b₁ b₂) : Equiv (insertTree a₁ b₁) (insertTree a₂ b₂) := by
  apply equiv_def.mpr
  intro x
  constructor
  · intro hx
    cases mem_of_mem_insertTree hx with
    | inl hl =>
      have hx_a2 : Equiv x a₂ := Equiv_trans hl ha
      have ha2_mem : Mem a₂ (insertTree a₂ b₂) := mem_insertTree_self a₂ b₂
      exact Equiv_Mem_trans hx_a2 ha2_mem
    | inr hr =>
      have hx_b2 : Mem x b₂ := Mem_Subset_trans hr hb.left
      exact mem_insertTree_of_mem hx_b2
  · intro hx
    cases mem_of_mem_insertTree hx with
    | inl hl =>
      have hx_a1 : Equiv x a₁ := Equiv_trans hl (Equiv_symm ha)
      have ha1_mem : Mem a₁ (insertTree a₁ b₁) := mem_insertTree_self a₁ b₁
      exact Equiv_Mem_trans hx_a1 ha1_mem
    | inr hr =>
      have hx_b1 : Mem x b₁ := Mem_Subset_trans hr hb.right
      exact mem_insertTree_of_mem hx_b1

def insert (a b : HCSet) : HCSet :=
  Quotient.lift₂ (fun x y => Quotient.mk CountableSets.Setoid (insertTree x y)) (fun _x1 _y1 _x2 _y2 hx hy => Quotient.sound (insertTree_respects hx hy)) a b

-- ══════════════════════════════════════════════════════════════════
-- § 3. Axioma de Infinito (ω)
-- ══════════════════════════════════════════════════════════════════

def natTree : ℕ₀ → Tree
  | Peano.ℕ₀.zero => .zero
  | Peano.ℕ₀.succ n => insertTree (natTree n) (natTree n)

def omegaTree : Tree := .sup natTree

def omega : HCSet := Quotient.mk CountableSets.Setoid omegaTree

end CountableSets
