/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

import Peano

open Peano

namespace CountableSets

/-- Árboles con ramificación a lo sumo numerable, la base para los Conjuntos Hereditariamente Numerables (HCSet). -/
inductive Tree : Type where
  | zero : Tree
  | succ : Tree → Tree
  | sup  : (ℕ₀ → Tree) → Tree

mutual
  /-- Relación de subconjunto (A ⊆ B) para conjuntos al estilo Aczel.
      A ⊆ B significa que todo elemento de A pertenece a B. -/
  inductive Subset : Tree → Tree → Prop where
    | zero_subset (y : Tree) : Subset .zero y
    | succ_subset {x y : Tree} : Mem x y → Subset (.succ x) y
    | sup_subset {f : ℕ₀ → Tree} {y : Tree} : (∀ n, Mem (f n) y) → Subset (.sup f) y

  /-- Relación de pertenencia (a ∈ B) al estilo Aczel.
      a ∈ B significa que `a` es equivalente a algún elemento que compone directamente a `B`. -/
  inductive Mem : Tree → Tree → Prop where
    | mem_succ {x y : Tree} : Subset x y → Subset y x → Mem x (.succ y)
    | mem_sup {x : Tree} {f : ℕ₀ → Tree} (n : ℕ₀) : Subset x (f n) → Subset (f n) x → Mem x (.sup f)
end

/-- Equivalencia extensional de Aczel (A ≡ B).
    Dos conjuntos son equivalentes si tienen los mismos elementos (A ⊆ B ∧ B ⊆ A). -/
def Equiv (x y : Tree) : Prop := Subset x y ∧ Subset y x

instance : Membership Tree Tree := ⟨fun y x => Mem x y⟩
instance : HasSubset Tree := ⟨Subset⟩

def Equiv.left {x y : Tree} (h : Equiv x y) : Subset x y := h.1
def Equiv.right {x y : Tree} (h : Equiv x y) : Subset y x := h.2

theorem Equiv.intro {x y : Tree} (h1 : Subset x y) (h2 : Subset y x) : Equiv x y := ⟨h1, h2⟩

theorem mem_succ_equiv {x y : Tree} (h : Equiv x y) : Mem x (.succ y) :=
  .mem_succ h.left h.right

theorem mem_sup_equiv {x : Tree} {f : ℕ₀ → Tree} (n : ℕ₀) (h : Equiv x (f n)) : Mem x (.sup f) :=
  .mem_sup n h.left h.right

def Subset_refl (x : Tree) : Subset x x :=
  match x with
  | .zero => .zero_subset .zero
  | .succ x => .succ_subset (.mem_succ (Subset_refl x) (Subset_refl x))
  | .sup f => .sup_subset fun n => .mem_sup n (Subset_refl (f n)) (Subset_refl (f n))

def trans_all (y : Tree) :
  (∀ {x z}, Subset x y → Subset y z → Subset x z) ∧
  (∀ {x z}, Mem x y → Subset y z → Mem x z) ∧
  (∀ {x z}, Subset y x → Subset x y → Mem y z → Mem x z) :=
  let mem_sub : ∀ {x z}, Mem x y → Subset y z → Mem x z := fun {_ z} h1 h2 =>
    match y, z, h2 with
    | _, _, .zero_subset _ => nomatch h1
    | _, _, @Subset.succ_subset a _ hmem2 =>
      match h1 with
      | @Mem.mem_succ _ _ hx_a ha_x => (trans_all a).2.2 ha_x hx_a hmem2
    | _, _, @Subset.sup_subset f _ hsub2 =>
      match h1 with
      | @Mem.mem_sup _ _ n hx_fn hfn_x => (trans_all (f n)).2.2 hfn_x hx_fn (hsub2 n)

  let sub_sub : ∀ {x z}, Subset x y → Subset y z → Subset x z := fun {x _} h1 h2 =>
    match x, h1 with
    | _, .zero_subset _ => .zero_subset _
    | _, @Subset.succ_subset d _ hmem => .succ_subset (mem_sub hmem h2)
    | _, @Subset.sup_subset f _ hsub => .sup_subset fun n => mem_sub (hsub n) h2

  let eq_mem : ∀ {x z}, Subset y x → Subset x y → Mem y z → Mem x z := fun {_ z} hyx hxy hyz =>
    match z, hyz with
    | _, @Mem.mem_succ _ b hyb hby =>
      .mem_succ (sub_sub hxy hyb) (sub_sub hby hyx)
    | _, @Mem.mem_sup _ g n hyg hgy =>
      .mem_sup n (sub_sub hxy hyg) (sub_sub hgy hyx)

  ⟨sub_sub, mem_sub, eq_mem⟩

theorem Subset_trans {x y z : Tree} (h1 : Subset x y) (h2 : Subset y z) : Subset x z :=
  (trans_all y).1 h1 h2

theorem Mem_Subset_trans {x y z : Tree} (h1 : Mem x y) (h2 : Subset y z) : Mem x z :=
  (trans_all y).2.1 h1 h2

theorem Equiv_Mem_trans {x y z : Tree} (hx : Equiv x y) (hyz : Mem y z) : Mem x z :=
  (trans_all y).2.2 hx.right hx.left hyz

theorem Equiv_refl (x : Tree) : Equiv x x :=
  ⟨Subset_refl x, Subset_refl x⟩

theorem Equiv_symm {x y : Tree} (h : Equiv x y) : Equiv y x :=
  ⟨h.right, h.left⟩

theorem Equiv_trans {x y z : Tree} (h1 : Equiv x y) (h2 : Equiv y z) : Equiv x z :=
  ⟨Subset_trans h1.left h2.left, Subset_trans h2.right h1.right⟩

instance Setoid : Setoid Tree where
  r := Equiv
  iseqv := {
    refl := Equiv_refl
    symm := Equiv_symm
    trans := Equiv_trans
  }

/-- Conjuntos Hereditariamente Numerables (HCSet) como cociente extensional -/
abbrev HCSet := Quotient CountableSets.Setoid

theorem Subset_respects {x₁ x₂ y₁ y₂ : Tree} (hx : Equiv x₁ x₂) (hy : Equiv y₁ y₂) : CountableSets.Subset x₁ y₁ = CountableSets.Subset x₂ y₂ :=
  propext ⟨fun h => Subset_trans (Subset_trans hx.right h) hy.left,
           fun h => Subset_trans (Subset_trans hx.left h) hy.right⟩

theorem Mem_respects {x₁ x₂ y₁ y₂ : Tree} (hx : Equiv x₁ x₂) (hy : Equiv y₁ y₂) : CountableSets.Mem x₁ y₁ = CountableSets.Mem x₂ y₂ :=
  propext ⟨fun h => Mem_Subset_trans (Equiv_Mem_trans (Equiv_symm hx) h) hy.left,
           fun h => Mem_Subset_trans (Equiv_Mem_trans hx h) hy.right⟩

def HCSet.Subset (a b : HCSet) : Prop :=
  Quotient.lift₂ CountableSets.Subset (fun _ _ _ _ (hx : Equiv _ _) (hy : Equiv _ _) => Subset_respects hx hy) a b

def HCSet.Mem (a b : HCSet) : Prop :=
  Quotient.lift₂ CountableSets.Mem (fun _ _ _ _ (hx : Equiv _ _) (hy : Equiv _ _) => Mem_respects hx hy) a b

instance : HasSubset HCSet := ⟨HCSet.Subset⟩
instance : Membership HCSet HCSet := ⟨fun y x => HCSet.Mem x y⟩

theorem HCSet.ext_iff (a b : HCSet) : a = b ↔ (a ⊆ b ∧ b ⊆ a) := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  exact ⟨fun h => ⟨(Quotient.exact h).1, (Quotient.exact h).2⟩, fun h => Quotient.sound ⟨h.1, h.2⟩⟩

theorem HCSet.ext {a b : HCSet} (h1 : a ⊆ b) (h2 : b ⊆ a) : a = b :=
  (ext_iff a b).mpr ⟨h1, h2⟩

end CountableSets
