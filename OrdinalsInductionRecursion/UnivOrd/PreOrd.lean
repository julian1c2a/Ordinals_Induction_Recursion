/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import Peano

open Peano

universe u

/-- El tipo de Pre-Ordinales de Von Neumann (árboles de Brouwer) universales. -/
inductive PreOrd : Type (u + 1) where
  | zero : PreOrd
  | succ : PreOrd → PreOrd
  | sup  : {α : Type u} → (α → PreOrd) → PreOrd

namespace PreOrd

mutual
  /-- Relación de subconjunto (≤) para los pre-ordinales -/
  inductive Subset : PreOrd.{u} → PreOrd.{u} → Prop where
    | zero_subset (y : PreOrd) : Subset zero y
    | succ_subset {x y : PreOrd} : Mem x y → Subset (succ x) y
    | sup_subset {α : Type u} {f : α → PreOrd} {y : PreOrd} : (∀ a, Subset (f a) y) → Subset (sup f) y

  /-- Relación de pertenencia (<) para los pre-ordinales -/
  inductive Mem : PreOrd.{u} → PreOrd.{u} → Prop where
    | mem_succ {x y : PreOrd} : Subset x y → Mem x (succ y)
    | mem_sup {α : Type u} {x : PreOrd} {f : α → PreOrd} (a : α) : Mem x (f a) → Mem x (sup f)
end

instance : Membership PreOrd PreOrd := ⟨Mem⟩
instance : HasSubset PreOrd := ⟨Subset⟩

/-- Igualdad extensional (equivalencia) de pre-ordinales -/
def Equiv (x y : PreOrd) : Prop := Subset x y ∧ Subset y x

-- ==========================================
-- Lemas de Equivalencia (Setoid)
-- ==========================================

theorem Subset_sup {y z : PreOrd} {α : Type u} {f : α → PreOrd}
  (h : Subset y z) (a : α) (hz : z = f a) :
    Subset y (sup f)
      :=
  match y, z, h with
  | _, _, .zero_subset _ => .zero_subset _
  | _, _, .succ_subset hmem => .succ_subset (Mem.mem_sup a (hz ▸ hmem))
  | _, _, .sup_subset hsub => .sup_subset fun k => Subset_sup (hsub k) a hz

theorem Subset_refl
  (x : PreOrd) :
    Subset x x
      :=
  match x with
  | .zero => .zero_subset _
  | .succ x' => .succ_subset (.mem_succ (Subset_refl x'))
  | .sup f => .sup_subset fun a => Subset_sup (Subset_refl (f a)) a rfl

theorem Mem_self_succ
  (x : PreOrd) :
    Mem x (succ x)
      :=
  .mem_succ (Subset_refl x)

def trans_all
  (x : PreOrd) :
    (∀ {y z}, Subset x y → Subset y z → Subset x z) ∧
    (∀ {y z}, Mem x y → Subset y z → Mem x z) ∧
    (∀ {y z}, Subset x y → Mem y z → Mem x z)
      :=
  let sub_sub : ∀ {y z}, Subset x y → Subset y z → Subset x z :=
    match x with
    | .zero => fun _ _ => .zero_subset _
    | .succ x' => fun h1 h2 =>
      match h1 with
      | @Subset.succ_subset _ _ hmem1 => .succ_subset ((trans_all x').2.1 hmem1 h2)
    | .sup f => fun h1 h2 =>
      match h1 with
      | @Subset.sup_subset _ _ _ hsub1 => .sup_subset fun a => (trans_all (f a)).1 (hsub1 a) h2

  let rec sub_mem {y z} (h1 : Subset x y) (h2 : Mem y z) : Mem x z :=
    match y, z, h2 with
    | _, _, .mem_succ hsub2 => .mem_succ (sub_sub h1 hsub2)
    | _, _, .mem_sup a hmem2 => .mem_sup a (sub_mem h1 hmem2)

  let rec mem_sub {y z} (h1 : Mem x y) (h2 : Subset y z) : Mem x z :=
    match y, z, h2 with
    | _, _, .zero_subset _ => nomatch h1
    | _, _, @Subset.succ_subset y' _ hmem2 =>
      match h1 with
      | @Mem.mem_succ _ _ hsub1 => sub_mem hsub1 hmem2
    | _, _, @Subset.sup_subset _ g _ hsub2 =>
      match h1 with
      | @Mem.mem_sup _ _ _ a hmem1 => mem_sub hmem1 (hsub2 a)

  ⟨sub_sub, mem_sub, sub_mem⟩

theorem Subset_trans {x y z : PreOrd} (h1 : Subset x y) (h2 : Subset y z) : Subset x z :=
  (trans_all x).1 h1 h2

theorem Mem_Subset_trans {x y z : PreOrd} (h1 : Mem x y) (h2 : Subset y z) : Mem x z :=
  (trans_all x).2.1 h1 h2

theorem Subset_Mem_trans {x y z : PreOrd} (h1 : Subset x y) (h2 : Mem y z) : Mem x z :=
  (trans_all x).2.2 h1 h2

theorem Equiv_refl (x : PreOrd) : Equiv x x :=
  ⟨Subset_refl x, Subset_refl x⟩

theorem Equiv_symm {x y : PreOrd} (h : Equiv x y) : Equiv y x :=
  ⟨h.right, h.left⟩

theorem Equiv_trans {x y z : PreOrd} (h1 : Equiv x y) (h2 : Equiv y z) : Equiv x z :=
  ⟨Subset_trans h1.left h2.left, Subset_trans h2.right h1.right⟩

instance Setoid : Setoid PreOrd where
  r := Equiv
  iseqv := {
    refl := Equiv_refl
    symm := Equiv_symm
    trans := Equiv_trans
  }

def preFromNat : ℕ₀ → PreOrd.{u}
  | .zero   => zero
  | .succ n => succ (preFromNat n)

instance : Coe ℕ₀ PreOrd.{u} := ⟨preFromNat⟩

def preomega : PreOrd.{u} := sup (α := ULift.{u, 0} ℕ₀) (fun n => preFromNat n.down)

end PreOrd
