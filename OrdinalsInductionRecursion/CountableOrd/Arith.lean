/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import OrdinalsInductionRecursion.CountableOrd.Ordinals
import OrdinalsInductionRecursion.CountableOrd.OrdinalsLattice
import OrdinalsInductionRecursion.CountableOrd.WellOrder

namespace CountableOrd
namespace PreOrd

/-- Suma de pre-ordinales -/
def add (a : PreOrd) : PreOrd → PreOrd
  | zero => a
  | succ b => succ (add a b)
  | sup f => sup (fun n => add a (f n))

theorem add_mono_left {a1 a2 : PreOrd} (h : Subset a1 a2) (b : PreOrd) : Subset (add a1 b) (add a2 b) := by
  induction b with
  | zero => exact h
  | succ b' ih => exact Subset.succ_subset (Mem.mem_succ ih)
  | sup f ih => exact Subset.sup_subset fun n => Subset_sup (ih n) n rfl

theorem le_add_right (a b : PreOrd) : Subset a (add a b) := by
  induction b with
  | zero => exact Subset_refl a
  | succ b' ih => exact mem_subset (Subset_Mem_trans ih (Mem_self_succ _))
  | sup f ih => exact Subset_sup (ih 0) 0 rfl

mutual
  def add_mono_right_sub (a : PreOrd) {b1 b2 : PreOrd} (h : Subset b1 b2) : Subset (add a b1) (add a b2) :=
    match b1, b2, h with
    | _, _, .zero_subset y => le_add_right a y
    | _, _, .succ_subset hmem => .succ_subset (add_mono_right_mem a hmem)
    | _, _, .sup_subset hsub => .sup_subset fun n => add_mono_right_sub a (hsub n)

  def add_mono_right_mem (a : PreOrd) {b1 b2 : PreOrd} (h : Mem b1 b2) : Mem (add a b1) (add a b2) :=
    match b1, b2, h with
    | _, _, .mem_succ hsub => .mem_succ (add_mono_right_sub a hsub)
    | _, _, .mem_sup n hmem => .mem_sup n (add_mono_right_mem a hmem)
end

theorem add_subset_add {a1 a2 b1 b2 : PreOrd} (ha : Subset a1 a2) (hb : Subset b1 b2) : Subset (add a1 b1) (add a2 b2) :=
  Subset_trans (add_mono_left ha b1) (add_mono_right_sub a2 hb)

theorem add_respects {a1 a2 b1 b2 : PreOrd} (ha : Equiv a1 a2) (hb : Equiv b1 b2) : Equiv (add a1 b1) (add a2 b2) :=
  ⟨add_subset_add ha.left hb.left, add_subset_add ha.right hb.right⟩

/-- Multiplicación de pre-ordinales -/
def mul (a : PreOrd) : PreOrd → PreOrd
  | zero => zero
  | succ b => add (mul a b) a
  | sup f => sup (fun n => mul a (f n))

theorem mul_mono_left {a1 a2 : PreOrd} (h : Subset a1 a2) (b : PreOrd) : Subset (mul a1 b) (mul a2 b) := by
  induction b with
  | zero => exact Subset_refl zero
  | succ b' ih => exact add_subset_add ih h
  | sup f ih => exact Subset.sup_subset fun n => Subset_sup (ih n) n rfl

mutual
  def mul_mono_right_sub (a : PreOrd) {b1 b2 : PreOrd} (h : Subset b1 b2) : Subset (mul a b1) (mul a b2) :=
    match b1, b2, h with
    | _, _, .zero_subset y => .zero_subset _
    | _, _, .succ_subset hmem => mul_mono_right_mem_add a hmem
    | _, _, .sup_subset hsub => .sup_subset fun n => mul_mono_right_sub a (hsub n)

  def mul_mono_right_mem_add (a : PreOrd) {b1 b2 : PreOrd} (h : Mem b1 b2) : Subset (add (mul a b1) a) (mul a b2) :=
    match b1, b2, h with
    | _, _, .mem_succ hsub => add_subset_add (mul_mono_right_sub a hsub) (Subset_refl a)
    | _, _, .mem_sup n hmem => Subset_sup (mul_mono_right_mem_add a hmem) n rfl
end

theorem mul_respects {a1 a2 b1 b2 : PreOrd} (ha : Equiv a1 a2) (hb : Equiv b1 b2) : Equiv (mul a1 b1) (mul a2 b2) :=
  ⟨Subset_trans (mul_mono_left ha.left b1) (mul_mono_right_sub a2 hb.left),
   Subset_trans (mul_mono_left ha.right b2) (mul_mono_right_sub a1 hb.right)⟩

open Classical

/-- Exponenciación auxiliar estructural de pre-ordinales -/
def pow_aux (a : PreOrd) : PreOrd → PreOrd
  | zero => succ zero
  | succ b => mul (pow_aux a b) a
  | sup f => sup (fun n => pow_aux a (f n))

theorem mul_subset_mul {a1 a2 b1 b2 : PreOrd} (ha : Subset a1 a2) (hb : Subset b1 b2) : Subset (mul a1 b1) (mul a2 b2) :=
  Subset_trans (mul_mono_left ha b1) (mul_mono_right_sub a2 hb)

theorem pow_aux_mono_left {a1 a2 : PreOrd} (h : Subset a1 a2) (b : PreOrd) : Subset (pow_aux a1 b) (pow_aux a2 b) := by
  induction b with
  | zero => exact Subset_refl _
  | succ b' ih => exact mul_subset_mul ih h
  | sup f ih => exact Subset.sup_subset fun n => Subset_sup (ih n) n rfl

theorem succ_subset_succ {x y : PreOrd} (h : Subset x y) : Subset (succ x) (succ y) :=
  Subset.succ_subset (Subset_Mem_trans h (Mem_self_succ y))

theorem le_add_zero_left (x : PreOrd) : Subset x (add zero x) := by
  induction x with
  | zero => exact Subset_refl _
  | succ x' ih => exact succ_subset_succ ih
  | sup f ih => exact Subset.sup_subset fun n => Subset_sup (ih n) n rfl

theorem le_mul_self_of_ge_one (x a : PreOrd) (ha : Subset (succ zero) a) : Subset x (mul x a) :=
  Subset_trans (le_add_zero_left x) (mul_mono_right_sub x ha)

theorem le_pow_aux_right (a b : PreOrd) (ha : Subset (succ zero) a) : Subset (succ zero) (pow_aux a b) := by
  induction b with
  | zero => exact Subset_refl _
  | succ b' ih => exact Subset_trans ih (le_mul_self_of_ge_one (pow_aux a b') a ha)
  | sup f ih => exact Subset_sup (ih 0) 0 rfl

mutual
  def pow_aux_mono_right_sub (a : PreOrd) (ha : Subset (succ zero) a) {b1 b2 : PreOrd} (h : Subset b1 b2) : Subset (pow_aux a b1) (pow_aux a b2) :=
    match b1, b2, h with
    | _, _, .zero_subset y => le_pow_aux_right a y ha
    | _, _, .succ_subset hmem => pow_aux_mono_right_mem_mul a ha hmem
    | _, _, .sup_subset hsub => .sup_subset fun n => pow_aux_mono_right_sub a ha (hsub n)

  def pow_aux_mono_right_mem_mul (a : PreOrd) (ha : Subset (succ zero) a) {b1 b2 : PreOrd} (h : Mem b1 b2) : Subset (mul (pow_aux a b1) a) (pow_aux a b2) :=
    match b1, b2, h with
    | _, _, .mem_succ hsub => mul_subset_mul (pow_aux_mono_right_sub a ha hsub) (Subset_refl a)
    | _, _, .mem_sup n hmem => Subset_sup (pow_aux_mono_right_mem_mul a ha hmem) n rfl
end

theorem pow_aux_respects_right (a : PreOrd) (ha : Subset (succ zero) a) {b1 b2 : PreOrd} (hb : Equiv b1 b2) : Equiv (pow_aux a b1) (pow_aux a b2) :=
  ⟨pow_aux_mono_right_sub a ha hb.left, pow_aux_mono_right_sub a ha hb.right⟩

theorem pow_aux_respects {a1 a2 b1 b2 : PreOrd} (ha1 : Subset (succ zero) a1) (ha2 : Subset (succ zero) a2) (ha : Equiv a1 a2) (hb : Equiv b1 b2) : Equiv (pow_aux a1 b1) (pow_aux a2 b2) :=
  ⟨Subset_trans (pow_aux_mono_left ha.left b1) ((pow_aux_respects_right a2 ha2 hb).left),
   Subset_trans (pow_aux_mono_left ha.right b2) ((pow_aux_respects_right a1 ha1 hb).right)⟩

noncomputable def pow (a b : PreOrd) : PreOrd :=
  if Equiv a zero then
    if Equiv b zero then succ zero else zero
  else
    pow_aux a b

theorem pow_respects {a1 a2 b1 b2 : PreOrd} (ha : Equiv a1 a2) (hb : Equiv b1 b2) : Equiv (pow a1 b1) (pow a2 b2) := by
  unfold pow
  by_cases h_a1 : Equiv a1 zero
  · have h_a2 : Equiv a2 zero := ⟨Subset_trans ha.right h_a1.left, Subset_trans h_a1.right ha.left⟩
    rw [if_pos h_a1, if_pos h_a2]
    by_cases h_b1 : Equiv b1 zero
    · have h_b2 : Equiv b2 zero := ⟨Subset_trans hb.right h_b1.left, Subset_trans h_b1.right hb.left⟩
      rw [if_pos h_b1, if_pos h_b2]
      exact Equiv_refl _
    · have h_b2 : ¬Equiv b2 zero := fun h => h_b1 ⟨Subset_trans hb.left h.left, Subset_trans h.right hb.right⟩
      rw [if_neg h_b1, if_neg h_b2]
      exact Equiv_refl _
  · have h_a2 : ¬Equiv a2 zero := fun h => h_a1 ⟨Subset_trans ha.left h.left, Subset_trans h.right ha.right⟩
    rw [if_neg h_a1, if_neg h_a2]
    have ha1_succ : Subset (succ zero) a1 :=
      match (total_prop a1 zero).2.2 with
      | Or.inl h => Subset.succ_subset h
      | Or.inr h => False.elim (h_a1 ⟨h, .zero_subset _⟩)
    have ha2_succ : Subset (succ zero) a2 :=
      match (total_prop a2 zero).2.2 with
      | Or.inl h => Subset.succ_subset h
      | Or.inr h => False.elim (h_a2 ⟨h, .zero_subset _⟩)
    exact pow_aux_respects ha1_succ ha2_succ ha hb

end PreOrd

namespace Ordinal

def add (x y : Ordinal) : Ordinal :=
  Quotient.lift₂ (fun a b => Quotient.mk PreOrd.Setoid (PreOrd.add a b))
    (fun _ _ _ _ ha hb => Quotient.sound (PreOrd.add_respects ha hb)) x y

instance : Add Ordinal where
  add := add

def mul (x y : Ordinal) : Ordinal :=
  Quotient.lift₂ (fun a b => Quotient.mk PreOrd.Setoid (PreOrd.mul a b))
    (fun _ _ _ _ ha hb => Quotient.sound (PreOrd.mul_respects ha hb)) x y

instance : Mul Ordinal where
  mul := mul

noncomputable def pow (x y : Ordinal) : Ordinal :=
  Quotient.lift₂ (fun a b => Quotient.mk PreOrd.Setoid (PreOrd.pow a b))
    (fun _ _ _ _ ha hb => Quotient.sound (PreOrd.pow_respects ha hb)) x y

noncomputable instance : Pow Ordinal Ordinal where
  pow := pow

end Ordinal
end CountableOrd
