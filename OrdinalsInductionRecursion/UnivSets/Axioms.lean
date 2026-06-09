/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import OrdinalsInductionRecursion.UnivSets.Tree

universe u

namespace UnivSets

noncomputable section

local instance (p : Prop) : Decidable p := Classical.propDecidable p

open Tree

-- ==========================================
-- Funciones Auxiliares Estructurales
-- ==========================================

/-- Extrae el tipo índice de un árbol -/
def indexType : Tree.{u} → Type u
  | @sup α _ => α

/-- Extrae la familia de subárboles de un árbol -/
def indexFun (t : Tree.{u}) : indexType t → Tree.{u} :=
  match t with
  | @sup _ f => f

theorem tree_eta (t : Tree.{u}) : t = sup (indexFun t) := by
  cases t
  rfl

-- ==========================================
-- 1. Conjunto Vacío
-- ==========================================

def emptyTree : Tree.{u} := sup (α := PEmpty.{u+1}) PEmpty.elim

def empty : USet.{u} := Quotient.mk Setoid emptyTree

theorem not_mem_empty (x : USet.{u}) : ¬ (x ∈ empty) := by
  induction x using Quotient.ind
  rename_i a
  intro h
  have h' : Tree.Mem a emptyTree := h
  cases h'
  rename_i a' _ _
  cases a'

-- ==========================================
-- 2. Adjunción (Insert)
-- ==========================================

def insertTree (a b : Tree.{u}) : Tree.{u} :=
  match b with
  | @sup β f => sup (α := Option β) fun
    | none => a
    | some x => f x

theorem subset_insertTree_right (a b : Tree.{u}) : Tree.Subset b (insertTree a b) := by
  cases b
  rename_i β f
  apply Tree.Subset.sup_subset
  intro y
  exact Tree.Mem.mem_sup (some y) (Tree.Subset_refl _) (Tree.Subset_refl _)

theorem mem_insertTree_self (a b : Tree.{u}) : Tree.Mem a (insertTree a b) := by
  cases b
  rename_i β f
  exact Tree.Mem.mem_sup none (Tree.Subset_refl _) (Tree.Subset_refl _)

theorem insertTree_mono_right (a : Tree.{u}) {b1 b2 : Tree.{u}} (h : Tree.Subset b1 b2) : Tree.Subset (insertTree a b1) (insertTree a b2) := by
  cases b1
  cases b2
  rename_i β1 f1 β2 f2
  cases h
  rename_i hsub
  apply Tree.Subset.sup_subset
  intro y
  cases y with
  | none => exact Tree.Mem.mem_sup none (Tree.Subset_refl _) (Tree.Subset_refl _)
  | some y' =>
    have hmem := hsub y'
    cases hmem
    rename_i a' h1 h2
    exact Tree.Mem.mem_sup (some a') h1 h2

theorem insertTree_respects (a1 a2 b1 b2 : Tree.{u}) (ha : Tree.Equiv a1 a2) (hb : Tree.Equiv b1 b2) : Tree.Equiv (insertTree a1 b1) (insertTree a2 b2) := by
  cases b1; cases b2
  rename_i β1 f1 β2 f2
  apply Tree.Equiv.intro
  · apply Tree.Subset.sup_subset
    intro y
    cases y with
    | none => exact Tree.Mem.mem_sup none ha.left ha.right
    | some y' =>
      have hmem := hb.left
      cases hmem
      rename_i hsub
      have hm := hsub y'
      cases hm
      rename_i a' h1 h2
      exact Tree.Mem.mem_sup (some a') h1 h2
  · apply Tree.Subset.sup_subset
    intro y
    cases y with
    | none => exact Tree.Mem.mem_sup none ha.right ha.left
    | some y' =>
      have hmem := hb.right
      cases hmem
      rename_i hsub
      have hm := hsub y'
      cases hm
      rename_i a' h1 h2
      exact Tree.Mem.mem_sup (some a') h1 h2

theorem mem_insertTree_of_mem {x a b : Tree.{u}} (h : Tree.Mem x b) : Tree.Mem x (insertTree a b) := by
  cases b
  rename_i β f
  cases h
  rename_i a' hx_fa hfa_x
  exact Tree.Mem.mem_sup (some a') hx_fa hfa_x

theorem mem_of_mem_insertTree {x a b : Tree.{u}} (h : Tree.Mem x (insertTree a b)) : Tree.Equiv x a ∨ Tree.Mem x b := by
  cases b
  rename_i β f
  cases h
  rename_i o hx h_x
  cases o with
  | none => exact Or.inl ⟨hx, h_x⟩
  | some b' => exact Or.inr (Tree.Mem.mem_sup b' hx h_x)

def insert (a b : USet.{u}) : USet.{u} :=
  Quotient.lift₂ (fun x y => Quotient.mk Tree.Setoid (insertTree x y))
    (fun _ _ _ _ ha hb => Quotient.sound (insertTree_respects _ _ _ _ ha hb)) a b

theorem mem_insert_iff (x a b : USet.{u}) : x ∈ insert a b ↔ x = a ∨ x ∈ b := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  induction x using Quotient.ind
  rename_i x_tree b_tree a_tree
  constructor
  · intro h
    cases mem_of_mem_insertTree h with
    | inl hl => exact Or.inl (Quotient.sound hl)
    | inr hr => exact Or.inr hr
  · rintro (h | h)
    · rw [← h]
      exact mem_insertTree_self a_tree b_tree
    · exact mem_insertTree_of_mem h

def pair (a b : USet.{u}) : USet.{u} := insert a (insert b empty)

theorem mem_pair_iff (x a b : USet.{u}) : x ∈ pair a b ↔ x = a ∨ x = b := by
  unfold pair
  rw [mem_insert_iff, mem_insert_iff]
  have h_empty : ¬ (x ∈ empty) := not_mem_empty x
  constructor
  · rintro (h | h | h)
    · exact Or.inl h
    · exact Or.inr h
    · contradiction
  · rintro (h | h)
    · exact Or.inl h
    · exact Or.inr (Or.inl h)

-- ==========================================
-- 3. Unión
-- ==========================================

def unionTree (a : Tree.{u}) : Tree.{u} :=
  match a with
  | @sup α f => sup (α := Σ x : α, indexType (f x)) fun p =>
    indexFun (f p.1) p.2

theorem unionTree_subset_unionTree {a1 a2 : Tree.{u}} (h : Tree.Subset a1 a2) : Tree.Subset (unionTree a1) (unionTree a2) := by
  cases a1; cases a2
  rename_i α1 f1 α2 f2
  cases h
  rename_i hsub
  apply Tree.Subset.sup_subset
  intro p
  let x1 := p.1
  let y1 := p.2
  have h_mem_f1_f2 := hsub x1
  cases h_mem_f1_f2
  rename_i x2 h_f1_sub_f2 h_f2_sub_f1
  have h_eta1 : f1 x1 = sup (indexFun (f1 x1)) := tree_eta (f1 x1)
  have h_eta2 : f2 x2 = sup (indexFun (f2 x2)) := tree_eta (f2 x2)
  rw [h_eta1] at h_f1_sub_f2
  cases h_f1_sub_f2
  rename_i h_inner
  have h_mem_y1 := h_inner y1
  rw [h_eta2] at h_mem_y1
  cases h_mem_y1
  rename_i y2 h_sub1 h_sub2
  exact Tree.Mem.mem_sup (⟨x2, y2⟩ : Σ x, indexType (f2 x)) h_sub1 h_sub2

theorem unionTree_respects (a1 a2 : Tree.{u}) (ha : Tree.Equiv a1 a2) : Tree.Equiv (unionTree a1) (unionTree a2) :=
  Tree.Equiv.intro (unionTree_subset_unionTree ha.left) (unionTree_subset_unionTree ha.right)

def union (a : USet.{u}) : USet.{u} :=
  Quotient.lift (fun x => Quotient.mk Tree.Setoid (unionTree x))
    (fun _ _ h => Quotient.sound (unionTree_respects _ _ h)) a

theorem mem_unionTree_of_mem_mem {y x A : Tree.{u}} (hyx : Tree.Mem y x) (hxa : Tree.Mem x A) : Tree.Mem y (unionTree A) := by
  cases A
  rename_i α f
  cases hxa
  rename_i a hsub_x_fa hsub_fa_x
  have h_y_fa : Tree.Mem y (f a) := Tree.Mem_Subset_trans hyx hsub_x_fa
  have h_eta : f a = sup (indexFun (f a)) := tree_eta (f a)
  rw [h_eta] at h_y_fa
  cases h_y_fa
  rename_i b hsub_y_fb hsub_fb_y
  exact Tree.Mem.mem_sup (⟨a, b⟩ : Σ x, indexType (f x)) hsub_y_fb hsub_fb_y

theorem exists_mem_of_mem_unionTree {y A : Tree.{u}} (hya : Tree.Mem y (unionTree A)) : ∃ x, Tree.Mem x A ∧ Tree.Mem y x := by
  cases A
  rename_i α f
  cases hya
  rename_i p hsub_y_fp hsub_fp_y
  let a := p.1
  let b := p.2
  have h_fa_A : Tree.Mem (f a) (sup f) := Tree.Mem.mem_sup a (Tree.Subset_refl _) (Tree.Subset_refl _)
  have h_eta : f a = sup (indexFun (f a)) := tree_eta (f a)
  have h_y_fa : Tree.Mem y (f a) := by
    rw [h_eta]
    exact Tree.Mem.mem_sup b hsub_y_fp hsub_fp_y
  exact ⟨f a, h_fa_A, h_y_fa⟩

theorem mem_union_of_mem_mem {y x A : USet.{u}} (hyx : y ∈ x) (hxa : x ∈ A) : y ∈ union A := by
  induction A using Quotient.ind
  rename_i a_tree
  induction x using Quotient.ind
  rename_i x_tree
  induction y using Quotient.ind
  rename_i y_tree
  exact mem_unionTree_of_mem_mem hyx hxa

theorem Tree.mem_sup_equiv_new {x : Tree.{u}} {α : Type u} {f : α → Tree.{u}} (a : α) (h : Tree.Equiv x (f a)) : Tree.Mem x (Tree.sup f) :=
  Tree.Mem.mem_sup a h.left h.right

theorem Tree.subset_iff {a b : Tree.{u}} : Tree.Subset a b ↔ ∀ x, Tree.Mem x a → Tree.Mem x b := by
  constructor
  · intro h x hx
    exact Tree.Mem_Subset_trans hx h
  · intro h
    cases a
    rename_i f
    apply Tree.Subset.sup_subset
    intro i
    have h_mem : Tree.Mem (f i) (Tree.sup f) := Tree.mem_sup_equiv_new i (Tree.Equiv_refl _)
    exact h (f i) h_mem

theorem uset_subset_iff {a b : USet.{u}} : a ⊆ b ↔ ∀ x, x ∈ a → x ∈ b := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  rename_i b_tree a_tree
  constructor
  · intro h x hx
    induction x using Quotient.ind
    rename_i x_tree
    exact Tree.Mem_Subset_trans hx h
  · intro h
    apply Tree.subset_iff.mpr
    intro x_tree hx
    have h' := h (Quotient.mk Tree.Setoid x_tree) hx
    exact h'

theorem exists_mem_of_mem_union {y A : USet.{u}} (hya : y ∈ union A) : ∃ x, x ∈ A ∧ y ∈ x := by
  induction A using Quotient.ind
  rename_i a_tree
  induction y using Quotient.ind
  rename_i y_tree
  have ⟨x_tree, hxA, hyx⟩ := exists_mem_of_mem_unionTree hya
  exact ⟨Quotient.mk Setoid x_tree, hxA, hyx⟩

theorem mem_union_iff (y A : USet.{u}) : y ∈ union A ↔ ∃ x, y ∈ x ∧ x ∈ A :=
  ⟨fun h =>
    let ⟨x, hxA, hyx⟩ := exists_mem_of_mem_union h
    ⟨x, hyx, hxA⟩,
   fun ⟨_x, hyx, hxA⟩ => mem_union_of_mem_mem hyx hxA⟩

-- ==========================================
-- 4. Conjunto Potencia (Power Set)
-- ==========================================

def powersetTree (a : Tree.{u}) : Tree.{u} :=
  match a with
  | @sup α f => sup (α := α → Bool) fun g =>
      sup (α := {i : α // g i = true}) fun j => f j.val

theorem powersetTree_respects (a1 a2 : Tree.{u}) (ha : Tree.Equiv a1 a2) : Tree.Equiv (powersetTree a1) (powersetTree a2) := by
  cases a1; cases a2
  rename_i α1 f1 α2 f2
  apply Tree.Equiv.intro
  · apply Tree.Subset.sup_subset
    intro g1
    let g2 : α2 → Bool := fun y =>
      if h : ∃ x : α1, g1 x = true ∧ Tree.Equiv (f1 x) (f2 y) then true else false
    apply Tree.Mem.mem_sup g2
    · apply Tree.Subset.sup_subset
      intro i
      have h1 := i.property
      have h_sub := ha.left
      cases h_sub; rename_i h_mem_func
      have hmem := h_mem_func i.val
      cases hmem
      rename_i j hsub1 hsub2
      have hequiv : Tree.Equiv (f1 i.val) (f2 j) := ⟨hsub1, hsub2⟩
      have h_exists : ∃ x : α1, g1 x = true ∧ Tree.Equiv (f1 x) (f2 j) := ⟨i.val, h1, hequiv⟩
      have hg2 : g2 j = true := by
        dsimp [g2]
        rw [if_pos h_exists]
      exact Tree.Mem.mem_sup ⟨j, hg2⟩ hsub1 hsub2
    · apply Tree.Subset.sup_subset
      intro j
      have h2 := j.property
      dsimp [g2] at h2
      split at h2
      · rename_i h_exists
        rcases h_exists with ⟨x, hg1, hequiv⟩
        exact Tree.Mem.mem_sup ⟨x, hg1⟩ hequiv.right hequiv.left
      · contradiction
  · apply Tree.Subset.sup_subset
    intro g2
    let g1 : α1 → Bool := fun x =>
      if h : ∃ y : α2, g2 y = true ∧ Tree.Equiv (f1 x) (f2 y) then true else false
    apply Tree.Mem.mem_sup g1
    · apply Tree.Subset.sup_subset
      intro j
      have h2 := j.property
      have h_sub := ha.right
      cases h_sub; rename_i h_mem_func
      have hmem := h_mem_func j.val
      cases hmem
      rename_i i hsub1 hsub2
      have hequiv : Tree.Equiv (f1 i) (f2 j.val) := ⟨hsub2, hsub1⟩
      have h_exists : ∃ y : α2, g2 y = true ∧ Tree.Equiv (f1 i) (f2 y) := ⟨j.val, h2, hequiv⟩
      have hg1 : g1 i = true := by
        dsimp [g1]
        rw [if_pos h_exists]
      exact Tree.Mem.mem_sup ⟨i, hg1⟩ hsub1 hsub2
    · apply Tree.Subset.sup_subset
      intro i
      have h1 := i.property
      dsimp [g1] at h1
      split at h1
      · rename_i h_exists
        rcases h_exists with ⟨y, hg2, hequiv⟩
        exact Tree.Mem.mem_sup ⟨y, hg2⟩ hequiv.left hequiv.right
      · contradiction

def powerset (a : USet.{u}) : USet.{u} :=
  Quotient.lift (fun x => Quotient.mk Tree.Setoid (powersetTree x))
    (fun _ _ h => Quotient.sound (powersetTree_respects _ _ h)) a

theorem mem_powerset_iff (x A : USet.{u}) : x ∈ powerset A ↔ x ⊆ A := by
  sorry

-- ==========================================
-- 5. Axioma de Reemplazo
-- ==========================================

def replTree (f : Tree.{u} → Tree.{u}) (a : Tree.{u}) : Tree.{u} :=
  match a with
  | @sup α g => sup (α := α) fun i => f (g i)

theorem replTree_respects (f : Tree.{u} → Tree.{u}) (hf : ∀ x y, Tree.Equiv x y → Tree.Equiv (f x) (f y)) (a1 a2 : Tree.{u}) (ha : Tree.Equiv a1 a2) : Tree.Equiv (replTree f a1) (replTree f a2) := by
  cases a1; cases a2
  rename_i α1 g1 α2 g2
  apply Tree.Equiv.intro
  · apply Tree.Subset.sup_subset
    intro i
    have h_sub := ha.left
    cases h_sub; rename_i h_mem_func
    have hmem := h_mem_func i
    cases hmem
    rename_i j hsub1 hsub2
    have hequiv : Tree.Equiv (g1 i) (g2 j) := ⟨hsub1, hsub2⟩
    have hequiv_f := hf _ _ hequiv
    exact Tree.Mem.mem_sup j hequiv_f.left hequiv_f.right
  · apply Tree.Subset.sup_subset
    intro j
    have h_sub := ha.right
    cases h_sub; rename_i h_mem_func
    have hmem := h_mem_func j
    cases hmem
    rename_i i hsub1 hsub2
    have hequiv : Tree.Equiv (g2 j) (g1 i) := ⟨hsub1, hsub2⟩
    have hequiv_f := hf _ _ hequiv
    exact Tree.Mem.mem_sup i hequiv_f.left hequiv_f.right

def repl (f : Tree.{u} → Tree.{u}) (hf : ∀ x y, Tree.Equiv x y → Tree.Equiv (f x) (f y)) (a : USet.{u}) : USet.{u} :=
  Quotient.lift (fun x => Quotient.mk Tree.Setoid (replTree f x))
    (fun _ _ h => Quotient.sound (replTree_respects f hf _ _ h)) a

def liftFun (f : Tree.{u} → Tree.{u}) (hf : ∀ x y, Tree.Equiv x y → Tree.Equiv (f x) (f y)) (x : USet.{u}) : USet.{u} :=
  Quotient.lift (fun t => Quotient.mk Tree.Setoid (f t))
    (fun a b hab => Quotient.sound (hf a b hab)) x

noncomputable def USet.out (x : USet.{u}) : Tree.{u} :=
  Classical.choose (Quotient.exists_rep x)

theorem USet.out_eq (x : USet.{u}) : Quotient.mk Tree.Setoid (USet.out x) = x :=
  Classical.choose_spec (Quotient.exists_rep x)

theorem mem_repl_iff (f : Tree.{u} → Tree.{u}) (hf : ∀ x y, Tree.Equiv x y → Tree.Equiv (f x) (f y)) (a y : USet.{u}) :
  y ∈ repl f hf a ↔ ∃ x ∈ a, y = liftFun f hf x := by
  induction a using Quotient.ind
  rename_i a_tree
  induction y using Quotient.ind
  rename_i y_tree
  constructor
  · intro hy
    have hy_mem : Tree.Mem y_tree (replTree f a_tree) := hy
    cases a_tree
    rename_i α g
    cases hy_mem
    rename_i i h_left h_right
    have h_x_mem : Tree.Mem (g i) (sup g) := Tree.Mem.mem_sup i (Tree.Subset_refl (g i)) (Tree.Subset_refl (g i))
    refine ⟨Quotient.mk Tree.Setoid (g i), h_x_mem, ?_⟩
    exact Quotient.sound ⟨h_left, h_right⟩
  · rintro ⟨x, hx_mem, hx_eq⟩
    induction x using Quotient.ind
    rename_i x_tree
    have hx_mem_tree : Tree.Mem x_tree a_tree := hx_mem
    cases a_tree
    rename_i α g
    cases hx_mem_tree
    rename_i i h_x_g_left h_x_g_right
    have h_y_tree_eq : Tree.Equiv y_tree (f x_tree) := Quotient.exact hx_eq
    have h_f_x_f_g : Tree.Equiv (f x_tree) (f (g i)) := hf x_tree (g i) ⟨h_x_g_left, h_x_g_right⟩
    have h_y_tree_equiv : Tree.Equiv y_tree (f (g i)) := Tree.Equiv_trans h_y_tree_eq h_f_x_f_g
    exact Tree.Mem.mem_sup i h_y_tree_equiv.left h_y_tree_equiv.right

-- ==========================================
-- 6. Axioma de Separación (Decidible)
-- ==========================================

def sepTree (P : Tree.{u} → Prop) [∀ x, Decidable (P x)] (a : Tree.{u}) : Tree.{u} :=
  match a with
  | @sup α f => sup (α := {i : α // P (f i)}) fun j => f j.val

theorem sepTree_respects (P : Tree.{u} → Prop) [∀ x, Decidable (P x)] (hP : ∀ x y, Tree.Equiv x y → (P x ↔ P y)) (a1 a2 : Tree.{u}) (ha : Tree.Equiv a1 a2) : Tree.Equiv (sepTree P a1) (sepTree P a2) := by
  cases a1; cases a2
  rename_i α1 f1 α2 f2
  apply Tree.Equiv.intro
  · apply Tree.Subset.sup_subset
    intro i
    have h_sub := ha.left
    cases h_sub; rename_i h_mem_func
    have hmem := h_mem_func i.val
    cases hmem
    rename_i j hsub1 hsub2
    have hequiv : Tree.Equiv (f1 i.val) (f2 j) := ⟨hsub1, hsub2⟩
    have hP2 : P (f2 j) := (hP _ _ hequiv).mp i.property
    exact Tree.Mem.mem_sup ⟨j, hP2⟩ hsub1 hsub2
  · apply Tree.Subset.sup_subset
    intro j
    have h_sub := ha.right
    cases h_sub; rename_i h_mem_func
    have hmem := h_mem_func j.val
    cases hmem
    rename_i i hsub1 hsub2
    have hequiv : Tree.Equiv (f2 j.val) (f1 i) := ⟨hsub1, hsub2⟩
    have hP1 : P (f1 i) := (hP _ _ hequiv).mp j.property
    exact Tree.Mem.mem_sup ⟨i, hP1⟩ hsub1 hsub2

def sep (P : Tree.{u} → Prop) [∀ x, Decidable (P x)] (hP : ∀ x y, Tree.Equiv x y → (P x ↔ P y)) (a : USet.{u}) : USet.{u} :=
  Quotient.lift (fun x => Quotient.mk Tree.Setoid (sepTree P x))
    (fun _ _ h => Quotient.sound (sepTree_respects P hP _ _ h)) a

def sepUSetP (P : Tree.{u} → Prop) (hP : ∀ x y, Tree.Equiv x y → (P x ↔ P y)) (x : USet.{u}) : Prop :=
  Quotient.lift P (fun a b hab => propext (hP a b hab)) x

theorem mem_sep_iff (P : Tree.{u} → Prop) [∀ x, Decidable (P x)] (hP : ∀ x y, Tree.Equiv x y → (P x ↔ P y)) (a y : USet.{u}) :
  y ∈ sep P hP a ↔ y ∈ a ∧ sepUSetP P hP y := by
  induction a using Quotient.ind
  rename_i a_tree
  induction y using Quotient.ind
  rename_i y_tree
  constructor
  · intro hy
    have hy_mem : Tree.Mem y_tree (sepTree P a_tree) := hy
    cases a_tree
    rename_i α g
    cases hy_mem
    rename_i j h_left h_right
    -- j : {i : α // P (g i)}
    have h_x_mem : Tree.Mem (g j.val) (sup g) := Tree.Mem.mem_sup j.val (Tree.Subset_refl _) (Tree.Subset_refl _)
    have h_P_gj : P (g j.val) := j.property
    have hy_in_a : Tree.Mem y_tree (sup g) := Tree.Equiv_Mem_trans ⟨h_left, h_right⟩ h_x_mem
    have h_P_y : P y_tree := (hP _ _ ⟨h_left, h_right⟩).mpr h_P_gj
    exact ⟨hy_in_a, h_P_y⟩
  · rintro ⟨hy_in_a, h_P_y⟩
    have hy_mem : Tree.Mem y_tree a_tree := hy_in_a
    have hP_ytree : P y_tree := h_P_y
    cases a_tree
    rename_i α g
    cases hy_mem
    rename_i i h_y_g_left h_y_g_right
    have h_P_gi : P (g i) := (hP y_tree (g i) ⟨h_y_g_left, h_y_g_right⟩).mp hP_ytree
    let j : {k : α // P (g k)} := ⟨i, h_P_gi⟩
    exact Tree.Mem.mem_sup j h_y_g_left h_y_g_right

end

theorem Tree.mem_wf : WellFounded Tree.Mem := by
  constructor
  intro a
  induction a with
  | sup f ih =>
    constructor
    intro y hy
    cases hy
    rename_i a' hsub1 hsub2
    constructor
    intro z hz
    have hz_f : Tree.Mem z (f a') := Tree.Mem_Subset_trans hz hsub1
    exact (ih a').inv hz_f

theorem uset_mem_wf : WellFounded (fun (x y : USet.{u}) => x ∈ y) := by
  constructor
  intro x
  induction x using Quotient.ind
  rename_i x_tree
  have hwf := Tree.mem_wf.apply x_tree
  induction hwf with
  | intro a _ ih =>
    constructor
    intro y hy
    induction y using Quotient.ind
    rename_i y_tree
    have h_mem_tree : Tree.Mem y_tree a := hy
    exact ih y_tree h_mem_tree

theorem wf_has_min {α : Type u} {r : α → α → Prop} (hwf : WellFounded r) (p : α → Prop) : (∃ x, p x) → ∃ m, p m ∧ ∀ x, r x m → ¬p x := by
  intro h
  apply Classical.byContradiction
  intro h_contra
  obtain ⟨x, hx⟩ := h
  revert hx
  have hwf_x := hwf.apply x
  induction hwf_x with
  | intro y _ ih =>
    intro hy
    have h_not_min : ¬ (p y ∧ ∀ z, r z y → ¬ p z) := fun h_min => h_contra ⟨y, h_min⟩
    have h_ex : ∃ z, r z y ∧ p z := by
      apply Classical.byContradiction
      intro h_none
      apply h_not_min
      constructor
      · exact hy
      · intro z hz hz_p
        exact h_none ⟨z, hz, hz_p⟩
    obtain ⟨z, hz, hz_p⟩ := h_ex
    exact ih z hz hz_p
-- ==========================================
-- 8. Axioma del Infinito (omega)
-- ==========================================

def natTree : Nat → Tree.{u}
  | 0 => emptyTree
  | n + 1 => insertTree (natTree n) (natTree n)

def omegaTree : Tree.{u} := Tree.sup (α := ULift.{u} Nat) fun n => natTree n.down

def omega : USet.{u} := Quotient.mk Tree.Setoid omegaTree

theorem empty_mem_omega : empty.{u} ∈ omega.{u} := by
  show Tree.Mem emptyTree omegaTree
  apply Tree.Mem.mem_sup (ULift.up 0)
  · apply Tree.Subset_refl
  · apply Tree.Subset_refl

theorem insert_mem_omega {y : USet.{u}} (hy : y ∈ omega.{u}) : insert y y ∈ omega.{u} := by
  induction y using Quotient.ind
  rename_i yTree
  have hy' : Tree.Mem yTree omegaTree := hy
  cases hy' with
  | mem_sup n h_equiv_left h_equiv_right =>
    show Tree.Mem (insertTree yTree yTree) omegaTree
    apply Tree.Mem.mem_sup (ULift.up (n.down + 1))
    · have h_equiv := insertTree_respects yTree (natTree n.down) yTree (natTree n.down) ⟨h_equiv_left, h_equiv_right⟩ ⟨h_equiv_left, h_equiv_right⟩
      exact h_equiv.left
    · have h_equiv := insertTree_respects yTree (natTree n.down) yTree (natTree n.down) ⟨h_equiv_left, h_equiv_right⟩ ⟨h_equiv_left, h_equiv_right⟩
      exact h_equiv.right

end UnivSets
