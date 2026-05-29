/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import OrdinalsInductionRecursion.PreOrd

namespace PreOrd

-- ==========================================
-- Intersección Parcial
-- ==========================================

partial def inter : PreOrd → PreOrd → PreOrd
  | zero, _ => zero
  | _, zero => zero
  | succ x, succ y => succ (inter x y)
  | sup f, y => sup (fun n => inter (f n) y)
  | succ x, sup g => sup (fun n => inter (succ x) (g n))

-- ==========================================
-- Unión e Intersección Ordinal
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

theorem union_respects {x₁ x₂ y₁ y₂ : PreOrd} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : union x₁ y₁ ≈ union x₂ y₂ :=
  ⟨Subset_trans (union_mono_left hx.left y₁) (union_mono_right x₂ hy.left),
   Subset_trans (union_mono_left hx.right y₂) (union_mono_right x₁ hy.right)⟩

theorem inter_respects {x₁ x₂ y₁ y₂ : PreOrd} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : inter x₁ y₁ ≈ inter x₂ y₂ := by sorry


def sUnion : PreOrd → PreOrd
  | .zero => .zero
  | .succ x => x
  | .sup f => sup (fun n => sUnion (f n))

mutual
  theorem sUnion_mono_mem {x y : PreOrd} (h : Mem x y) : Subset (sUnion x) y :=
    match y, h with
    | _, .mem_succ hsub => hsub
    | _, .mem_sup n hmem => Subset_sup (sUnion_mono_mem hmem) n rfl

  theorem sUnion_mono_subset {x y : PreOrd} (h : Subset x y) : Subset (sUnion x) (sUnion y) :=
    match x, y, h with
    | _, _, .zero_subset _ => .zero_subset _
    | _, _, .succ_subset hmem => sUnion_mono_mem hmem
    | _, _, .sup_subset hsub => .sup_subset fun n => sUnion_mono_subset (hsub n)
end

theorem sUnion_respects {x y : PreOrd} (h : x ≈ y) : sUnion x ≈ sUnion y :=
  ⟨sUnion_mono_subset h.left, sUnion_mono_subset h.right⟩

def sInter : PreOrd → PreOrd
  | _ => zero

theorem sInter_respects {x y : PreOrd} (h : x ≈ y) : sInter x ≈ sInter y :=
  ⟨Subset_refl _, Subset_refl _⟩

-- ==========================================
-- Aritmética Ordinal y Respeto de Equivalencia
-- ==========================================

def add (x : PreOrd) : PreOrd → PreOrd
  | zero   => x
  | succ y => succ (add x y)
  | sup f  => sup (fun n => add x (f n))

theorem add_mono_left_subset {x₁ x₂ : PreOrd} (h : Subset x₁ x₂) (y : PreOrd) : Subset (add x₁ y) (add x₂ y) :=
  match y with
  | .zero => h
  | .succ y' => .succ_subset (.mem_succ (add_mono_left_subset h y'))
  | .sup f => .sup_subset fun n => add_mono_left_subset h (f n)

mutual
  theorem Mem_to_Subset {a b : PreOrd} (h : Mem a b) : Subset a b :=
    match b, h with
    | _, .mem_succ hsub => Subset_succ hsub
    | _, .mem_sup n hmem => Subset_sup (Mem_to_Subset hmem) n rfl

  theorem Subset_succ {a b : PreOrd} (h : Subset a b) : Subset a (succ b) :=
    match a, h with
    | _, .zero_subset _ => .zero_subset _
    | _, .succ_subset hmem => .succ_subset (.mem_succ (Mem_to_Subset hmem))
    | _, .sup_subset hsub => .sup_subset fun n => Subset_succ (hsub n)
end

theorem Subset_add_left (x y : PreOrd) : Subset x (add x y) :=
  match y with
  | .zero => Subset_refl x
  | .succ y' => Subset_succ (Subset_add_left x y')
  | .sup f => Subset_sup (Subset_add_left x (f .zero)) .zero rfl

mutual
  theorem add_mono_right_subset (x : PreOrd) {y₁ y₂ : PreOrd} (h : Subset y₁ y₂) : Subset (add x y₁) (add x y₂) :=
    match y₁, y₂, h with
    | _, _, .zero_subset _ => Subset_add_left x y₂
    | _, _, .succ_subset hmem => .succ_subset (add_mono_right_mem x hmem)
    | _, _, .sup_subset hsub => .sup_subset fun n => add_mono_right_subset x (hsub n)

  theorem add_mono_right_mem (x : PreOrd) {y₁ y₂ : PreOrd} (h : Mem y₁ y₂) : Mem (add x y₁) (add x y₂) :=
    match y₁, y₂, h with
    | _, _, .mem_succ hsub => .mem_succ (add_mono_right_subset x hsub)
    | _, _, .mem_sup n hmem => .mem_sup n (add_mono_right_mem x hmem)
end

theorem Subset_add {x₁ x₂ y₁ y₂ : PreOrd} (hx : Subset x₁ x₂) (hy : Subset y₁ y₂) : Subset (add x₁ y₁) (add x₂ y₂) :=
  Subset_trans (add_mono_left_subset hx y₁) (add_mono_right_subset x₂ hy)

theorem add_respects {x₁ x₂ y₁ y₂ : PreOrd} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : add x₁ y₁ ≈ add x₂ y₂ :=
  ⟨Subset_add hx.left hy.left, Subset_add hx.right hy.right⟩

def mul (x : PreOrd) : PreOrd → PreOrd
  | zero   => zero
  | succ y => add (mul x y) x
  | sup f  => sup (fun n => mul x (f n))

theorem mul_mono_left_subset {x₁ x₂ : PreOrd} (h : Subset x₁ x₂) (y : PreOrd) : Subset (mul x₁ y) (mul x₂ y) :=
  match y with
  | .zero => .zero_subset _
  | .succ y' => Subset_add (mul_mono_left_subset h y') h
  | .sup f => .sup_subset fun n => mul_mono_left_subset h (f n)

mutual
  theorem mul_mono_right_subset (x : PreOrd) {y₁ y₂ : PreOrd} (h : Subset y₁ y₂) : Subset (mul x y₁) (mul x y₂) :=
    match y₁, y₂, h with
    | _, _, .zero_subset _ => .zero_subset _
    | _, _, .succ_subset hmem => mul_mono_right_mem x hmem
    | _, _, .sup_subset hsub => .sup_subset fun n => mul_mono_right_subset x (hsub n)

  theorem mul_mono_right_mem (x : PreOrd) {a b : PreOrd} (h : Mem a b) : Subset (add (mul x a) x) (mul x b) :=
    match b, h with
    | _, .mem_succ hsub => Subset_add (mul_mono_right_subset x hsub) (Subset_refl x)
    | _, .mem_sup n hmem => Subset_sup (mul_mono_right_mem x hmem) n rfl
end

theorem Subset_mul {x₁ x₂ y₁ y₂ : PreOrd} (hx : Subset x₁ x₂) (hy : Subset y₁ y₂) : Subset (mul x₁ y₁) (mul x₂ y₂) :=
  Subset_trans (mul_mono_left_subset hx y₁) (mul_mono_right_subset x₂ hy)

theorem mul_respects {x₁ x₂ y₁ y₂ : PreOrd} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : mul x₁ y₁ ≈ mul x₂ y₂ :=
  ⟨Subset_mul hx.left hy.left, Subset_mul hx.right hy.right⟩

def pow (x : PreOrd) : PreOrd → PreOrd
  | zero   => succ zero
  | succ y => mul (pow x y) x
  | sup f  => sup (fun n => pow x (f n))

theorem pow_respects {x₁ x₂ y₁ y₂ : PreOrd} (hx : x₁ ≈ x₂) (hy : y₁ ≈ y₂) : pow x₁ y₁ ≈ pow x₂ y₂ := by sorry

end PreOrd

-- ==========================================
-- Tipo Cociente: Ord
-- ==========================================

/-- El tipo de Ordinales de Von Neumann, definido como el cociente
    de los Pre-Ordinales respecto a la igualdad extensional -/
def Ord := Quotient PreOrd.Setoid

namespace Ord

def union (x y : Ord) : Ord :=
  Quotient.lift₂ (fun a b => ⟦PreOrd.union a b⟧) (fun _ _ _ _ hx hy => Quotient.sound (PreOrd.union_respects hx hy)) x y

def inter (x y : Ord) : Ord :=
  Quotient.lift₂ (fun a b => ⟦PreOrd.inter a b⟧) (fun _ _ _ _ hx hy => Quotient.sound (PreOrd.inter_respects hx hy)) x y

def add (x y : Ord) : Ord :=
  Quotient.lift₂ (fun a b => ⟦PreOrd.add a b⟧) (fun _ _ _ _ hx hy => Quotient.sound (PreOrd.add_respects hx hy)) x y

def mul (x y : Ord) : Ord :=
  Quotient.lift₂ (fun a b => ⟦PreOrd.mul a b⟧) (fun _ _ _ _ hx hy => Quotient.sound (PreOrd.mul_respects hx hy)) x y

def pow (x y : Ord) : Ord :=
  Quotient.lift₂ (fun a b => ⟦PreOrd.pow a b⟧) (fun _ _ _ _ hx hy => Quotient.sound (PreOrd.pow_respects hx hy)) x y

def sUnion (x : Ord) : Ord :=
  Quotient.lift (fun a => ⟦PreOrd.sUnion a⟧) (fun _ _ h => Quotient.sound (PreOrd.sUnion_respects h)) x

def sInter (x : Ord) : Ord :=
  Quotient.lift (fun a => ⟦PreOrd.sInter a⟧) (fun _ _ h => Quotient.sound (PreOrd.sInter_respects h)) x

instance : Add Ord := ⟨add⟩
instance : Mul Ord := ⟨mul⟩

def omega : Ord := ⟦PreOrd.omega⟧
notation "ω" => omega

end Ord
