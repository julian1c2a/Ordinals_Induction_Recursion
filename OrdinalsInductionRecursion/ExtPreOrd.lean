/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import OrdinalsInductionRecursion.PreOrd

namespace PreOrd

-- ==========================================
-- Lemas de Equivalencia para Relaciones
-- ==========================================

theorem Subset_respects {x₁ x₂ y₁ y₂ : PreOrd} (hx : Equiv x₁ x₂) (hy : Equiv y₁ y₂) : Subset x₁ y₁ = Subset x₂ y₂ :=
  propext ⟨fun h => Subset_trans (Subset_trans hx.right h) hy.left,
           fun h => Subset_trans (Subset_trans hx.left h) hy.right⟩

theorem Mem_respects {x₁ x₂ y₁ y₂ : PreOrd} (hx : Equiv x₁ x₂) (hy : Equiv y₁ y₂) : Mem x₁ y₁ = Mem x₂ y₂ :=
  propext ⟨fun h => Mem_Subset_trans (Subset_Mem_trans hx.right h) hy.left,
           fun h => Mem_Subset_trans (Subset_Mem_trans hx.left h) hy.right⟩


-- ==========================================
-- Intersección Parcial
-- ==========================================

def inter_succ_y (ih_x : PreOrd → PreOrd) : PreOrd → PreOrd
  | .zero => .zero
  | .succ y' => .succ (ih_x y')
  | .sup g => .sup (fun n => inter_succ_y ih_x (g n))

def inter (x : PreOrd) : PreOrd → PreOrd :=
  match x with
  | .zero => fun _ => .zero
  | .sup f => fun y => .sup (fun n => inter (f n) y)
  | .succ x' => inter_succ_y (inter x')

theorem zero_inter_subset (y : PreOrd) : Subset (inter zero y) zero :=
  .zero_subset _

theorem inter_zero_subset (x : PreOrd) : Subset (inter x zero) zero :=
  match x with
  | .zero => .zero_subset _
  | .succ _ => .zero_subset _
  | .sup f => .sup_subset fun n => inter_zero_subset (f n)

mutual
  theorem inter_mono_right_subset_succ (x' : PreOrd)
    (ih_subset : ∀ {y₁ y₂}, Subset y₁ y₂ → Subset (inter x' y₁) (inter x' y₂))
    {y₁ y₂ : PreOrd} (h : Subset y₁ y₂) : Subset (inter (succ x') y₁) (inter (succ x') y₂) :=
    match y₁, y₂, h with
    | _, _, .zero_subset _ => Subset_trans (inter_zero_subset _) (.zero_subset _)
    | _, _, .succ_subset hmem => inter_mono_right_mem_succ x' @ih_subset hmem
    | _, _, .sup_subset hsub => .sup_subset fun n => inter_mono_right_subset_succ x' @ih_subset (hsub n)

  theorem inter_mono_right_mem_succ (x' : PreOrd)
    (ih_subset : ∀ {y₁ y₂}, Subset y₁ y₂ → Subset (inter x' y₁) (inter x' y₂))
    {y₁ y₂ : PreOrd} (h : Mem y₁ y₂) : Subset (inter (succ x') (succ y₁)) (inter (succ x') y₂) :=
    match y₂, h with
    | _, .mem_succ hsub => .succ_subset (.mem_succ (ih_subset hsub))
    | _, .mem_sup n hmem =>
      Subset_trans (inter_mono_right_mem_succ x' @ih_subset hmem)
        (Subset_sup (f := fun _ => inter (succ x') _) (Subset_refl _) n rfl)
end

theorem inter_mono_right_subset (x : PreOrd) {y₁ y₂ : PreOrd} (h : Subset y₁ y₂) : Subset (inter x y₁) (inter x y₂) :=
  match x with
  | .zero => Subset_trans (inter_zero_subset zero) (.zero_subset _)
  | .sup f => .sup_subset fun n => Subset_sup (f := fun k => inter (f k) y₂) (inter_mono_right_subset (f n) h) n rfl
  | .succ x' => inter_mono_right_subset_succ x' (fun h' => inter_mono_right_subset x' h') h

theorem inter_mono_right_mem (x : PreOrd) {y₁ y₂ : PreOrd} (h : Mem y₁ y₂) : Subset (inter x (succ y₁)) (inter x y₂) :=
  match x with
  | .zero => .zero_subset _
  | .sup f => .sup_subset fun n => Subset_sup (f := fun k => inter (f k) y₂) (inter_mono_right_mem (f n) h) n rfl
  | .succ x' => inter_mono_right_mem_succ x' (fun h' => inter_mono_right_subset x' h') h

theorem inter_mono_left_mem_mem_succ {x₁ x₂' : PreOrd} (hsub : Subset x₁ x₂')
  (ih_subset : ∀ y, Subset (inter x₁ y) (inter x₂' y)) (y : PreOrd) :
  Subset (inter (succ x₁) y) (inter (succ x₂') y) :=
  match y with
  | .zero => .zero_subset _
  | .succ y' => .succ_subset (.mem_succ (ih_subset y'))
  | .sup g => .sup_subset fun n => Subset_sup (f := fun k => inter (succ x₂') (g k)) (inter_mono_left_mem_mem_succ hsub ih_subset (g n)) n rfl

mutual
  theorem inter_mono_left_subset {x₁ x₂ : PreOrd} (h : Subset x₁ x₂) (y : PreOrd) : Subset (inter x₁ y) (inter x₂ y) :=
    match x₁, x₂, h with
    | _, _, .zero_subset _ => Subset_trans (zero_inter_subset y) (.zero_subset _)
    | _, _, .succ_subset hmem => inter_mono_left_mem hmem y
    | _, _, .sup_subset hsub => .sup_subset fun n => inter_mono_left_subset (hsub n) y

  theorem inter_mono_left_mem {x₁ x₂ : PreOrd} (h : Mem x₁ x₂) (y : PreOrd) : Subset (inter (succ x₁) y) (inter x₂ y) :=
    match x₂, h with
    | .succ _, .mem_succ hsub => inter_mono_left_mem_mem_succ hsub (fun y => inter_mono_left_subset hsub y) y
    | .sup f, .mem_sup n hmem =>
      Subset_trans (inter_mono_left_mem hmem y) (Subset_sup (f := fun k => inter (f k) y) (Subset_refl _) n rfl)
end

theorem inter_respects {x₁ x₂ y₁ y₂ : PreOrd} (hx : Equiv x₁ x₂) (hy : Equiv y₁ y₂) : Equiv (inter x₁ y₁) (inter x₂ y₂) :=
  ⟨Subset_trans (inter_mono_left_subset hx.left y₁) (inter_mono_right_subset x₂ hy.left),
   Subset_trans (inter_mono_left_subset hx.right y₂) (inter_mono_right_subset x₁ hy.right)⟩


-- ==========================================
-- Unión Binaria
-- ==========================================

def union (x y : PreOrd) : PreOrd :=
  sup (fun n => match n with
    | .zero => x
    | .succ _ => y)

theorem union_mono_left {x₁ x₂ : PreOrd} (h : Subset x₁ x₂) (y : PreOrd) : Subset (union x₁ y) (union x₂ y) :=
  Subset.sup_subset fun n => match n with
    | .zero => Subset_trans h (Subset_sup (Subset_refl x₂) .zero rfl)
    | .succ m => Subset_sup (Subset_refl y) (.succ m) rfl

theorem union_mono_right (x : PreOrd) {y₁ y₂ : PreOrd} (h : Subset y₁ y₂) : Subset (union x y₁) (union x y₂) :=
  Subset.sup_subset fun n => match n with
    | .zero => Subset_sup (Subset_refl x) .zero rfl
    | .succ m => Subset_trans h (Subset_sup (Subset_refl y₂) (.succ m) rfl)

theorem union_respects {x₁ x₂ y₁ y₂ : PreOrd} (hx : Equiv x₁ x₂) (hy : Equiv y₁ y₂) : Equiv (union x₁ y₁) (union x₂ y₂) :=
  ⟨Subset_trans (union_mono_left hx.left y₁) (union_mono_right x₂ hy.left),
   Subset_trans (union_mono_left hx.right y₂) (union_mono_right x₁ hy.right)⟩


-- ==========================================
-- Unión e Intersección General
-- ==========================================

def sUnion : PreOrd → PreOrd
  | .zero => .zero
  | .succ x => x
  | .sup f => sup (fun n => sUnion (f n))

mutual
  theorem mem_subset {a b : PreOrd} (h : Mem a b) : Subset a b :=
    match b, h with
    | _, .mem_succ hsub => subset_succ_mono hsub
    | _, .mem_sup n hmem => Subset_sup (mem_subset hmem) n rfl

  theorem subset_succ_mono {a b : PreOrd} (h : Subset a b) : Subset a (succ b) :=
    match a, b, h with
    | _, _, .zero_subset _ => .zero_subset _
    | _, _, .succ_subset hmem => .succ_subset (.mem_succ (mem_subset hmem))
    | _, _, .sup_subset hsub => .sup_subset fun n => subset_succ_mono (hsub n)
end

theorem sUnion_subset_self (x : PreOrd) : Subset (sUnion x) x :=
  match x with
  | .zero => .zero_subset _
  | .succ x' => subset_succ_mono (Subset_refl x')
  | .sup f => .sup_subset fun n => Subset_sup (sUnion_subset_self (f n)) n rfl

theorem sUnion_mono_mem {x y : PreOrd} (h : Mem x y) : Subset (sUnion x) y :=
  Subset_trans (sUnion_subset_self x) (mem_subset h)

theorem mem_sUnion {a b : PreOrd} (h : Mem a b) : Subset a (sUnion b) :=
  match b, h with
  | _, .mem_succ hsub => hsub
  | _, .mem_sup n hmem => Subset_sup (mem_sUnion hmem) n rfl

theorem sUnion_mono_subset {x y : PreOrd} (h : Subset x y) : Subset (sUnion x) (sUnion y) :=
  match x, y, h with
  | _, _, .zero_subset _ => .zero_subset _
  | _, _, .succ_subset hmem => mem_sUnion hmem
  | _, _, .sup_subset hsub => .sup_subset fun n => sUnion_mono_subset (hsub n)

theorem sUnion_respects {x y : PreOrd} (h : Equiv x y) : Equiv (sUnion x) (sUnion y) :=
  ⟨sUnion_mono_subset h.left, sUnion_mono_subset h.right⟩

def sInter : PreOrd → PreOrd
  | _ => zero

theorem sInter_respects {x y : PreOrd} (_ : Equiv x y) : Equiv (sInter x) (sInter y) :=
  ⟨Subset_refl _, Subset_refl _⟩

end PreOrd
