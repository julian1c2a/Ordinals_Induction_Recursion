/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import OrdinalsInductionRecursion.UnivSets.Tree

universe u

namespace UnivSets

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

def insert (a b : USet.{u}) : USet.{u} :=
  Quotient.lift₂ (fun x y => Quotient.mk Tree.Setoid (insertTree x y))
    (fun _ _ _ _ ha hb => Quotient.sound (insertTree_respects _ _ _ _ ha hb)) a b

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

theorem exists_mem_of_mem_union {y A : USet.{u}} (hya : y ∈ union A) : ∃ x, x ∈ A ∧ y ∈ x := by
  induction A using Quotient.ind
  rename_i a_tree
  induction y using Quotient.ind
  rename_i y_tree
  have ⟨x_tree, hxA, hyx⟩ := exists_mem_of_mem_unionTree hya
  exact ⟨Quotient.mk Setoid x_tree, hxA, hyx⟩

end UnivSets
