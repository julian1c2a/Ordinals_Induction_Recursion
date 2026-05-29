/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import Peano

open Peano

/-- El tipo de Pre-Ordinales de Von Neumann (árboles de Brouwer). -/
inductive PreOrd : Type where
  | zero : PreOrd
  | succ : PreOrd → PreOrd
  | sup  : (ℕ₀ → PreOrd) → PreOrd

namespace PreOrd

mutual
  /-- Relación de subconjunto (≤) para los pre-ordinales -/
  inductive Subset : PreOrd → PreOrd → Prop where
    | zero_subset (y : PreOrd) : Subset zero y
    | succ_subset {x y : PreOrd} : Mem x y → Subset (succ x) y
    | sup_subset {f : ℕ₀ → PreOrd} {y : PreOrd} : (∀ n, Subset (f n) y) → Subset (sup f) y

  /-- Relación de pertenencia (<) para los pre-ordinales -/
  inductive Mem : PreOrd → PreOrd → Prop where
    | mem_succ {x y : PreOrd} : Subset x y → Mem x (succ y)
    | mem_sup {x : PreOrd} {f : ℕ₀ → PreOrd} (n : ℕ₀) : Mem x (f n) → Mem x (sup f)
end

instance : Membership PreOrd PreOrd := ⟨Mem⟩
instance : HasSubset PreOrd := ⟨Subset⟩

/-- Igualdad extensional (equivalencia) de pre-ordinales -/
def Equiv (x y : PreOrd) : Prop := Subset x y ∧ Subset y x

notation:50 x " ≈ " y => Equiv x y

-- ==========================================
-- Lemas de Equivalencia (Setoid)
-- ==========================================

theorem Subset_sup {y z : PreOrd} (h : Subset y z) {f : ℕ₀ → PreOrd} (n : ℕ₀) (hz : z = f n) : Subset y (sup f) :=
  match y, z, h with
  | _, _, .zero_subset _ => .zero_subset _
  | _, _, .succ_subset hmem => .succ_subset (Mem.mem_sup n (hz ▸ hmem))
  | _, _, .sup_subset hsub => .sup_subset fun k => Subset_sup (hsub k) n hz

mutual
  theorem Subset_refl (x : PreOrd) : Subset x x :=
    match x with
    | .zero => .zero_subset _
    | .succ x' => .succ_subset (Mem_self_succ x')
    | .sup f => .sup_subset fun n => Subset_sup (Subset_refl (f n)) n rfl

  theorem Mem_self_succ (x : PreOrd) : Mem x (succ x) :=
    .mem_succ (Subset_refl x)
end

mutual
  theorem Subset_trans {x y z : PreOrd} (h1 : Subset x y) (h2 : Subset y z) : Subset x z :=
    match x, y, h1 with
    | _, _, .zero_subset _ => .zero_subset _
    | _, _, .succ_subset hmem1 => .succ_subset (Mem_Subset_trans hmem1 h2)
    | _, _, .sup_subset hsub1 => .sup_subset fun n => Subset_trans (hsub1 n) h2

  theorem Mem_Subset_trans {x y z : PreOrd} (h1 : Mem x y) (h2 : Subset y z) : Mem x z :=
    match y, z, h2 with
    | _, _, .zero_subset _ => nomatch h1
    | _, _, .succ_subset hmem2 =>
      match x, y, h1 with
      | _, _, .mem_succ hsub1 => Subset_Mem_trans hsub1 hmem2
    | _, _, .sup_subset hsub2 =>
      match x, y, h1 with
      | _, _, .mem_sup n hmem1 => Mem_Subset_trans hmem1 (hsub2 n)

  theorem Subset_Mem_trans {x y z : PreOrd} (h1 : Subset x y) (h2 : Mem y z) : Mem x z :=
    match y, z, h2 with
    | _, _, .mem_succ hsub2 => .mem_succ (Subset_trans h1 hsub2)
    | _, _, .mem_sup n hmem2 => .mem_sup n (Subset_Mem_trans h1 hmem2)
end

theorem Equiv_refl (x : PreOrd) : x ≈ x :=
  ⟨Subset_refl x, Subset_refl x⟩

theorem Equiv_symm {x y : PreOrd} (h : x ≈ y) : y ≈ x :=
  ⟨h.right, h.left⟩

theorem Equiv_trans {x y z : PreOrd} (h1 : x ≈ y) (h2 : y ≈ z) : x ≈ z :=
  ⟨Subset_trans h1.left h2.left, Subset_trans h2.right h1.right⟩

instance Setoid : Setoid PreOrd where
  r := Equiv
  iseqv := {
    refl := Equiv_refl
    symm := Equiv_symm
    trans := Equiv_trans
  }

def fromNat : ℕ₀ → PreOrd
  | .zero   => zero
  | .succ n => succ (fromNat n)

def omega : PreOrd := sup fromNat
notation "ω" => omega

end PreOrd
