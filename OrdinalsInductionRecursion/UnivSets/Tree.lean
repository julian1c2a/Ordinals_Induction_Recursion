/-
Copyright (c) 2026. All rights reserved.
Author: Julián Calderón Almendros
License: MIT
-/

universe u

namespace UnivSets

/-- Árboles de Aczel (W-types) para el Universo de Conjuntos de Von Neumann. -/
inductive Tree : Type (u + 1) where
  | sup : {α : Type u} → (α → Tree) → Tree

namespace Tree

mutual
  /-- Relación de subconjunto (A ⊆ B) para conjuntos al estilo Aczel.
      A ⊆ B significa que todo elemento de A pertenece a B. -/
  inductive Subset : Tree.{u} → Tree.{u} → Prop where
    | sup_subset {α : Type u} {f : α → Tree} {y : Tree} :
        (∀ a, Mem (f a) y) → Subset (sup f) y

  /-- Relación de pertenencia (a ∈ B) al estilo Aczel.
      a ∈ B significa que `a` es equivalente a algún elemento que compone directamente a `B`. -/
  inductive Mem : Tree.{u} → Tree.{u} → Prop where
    | mem_sup {α : Type u} {x : Tree} {f : α → Tree} (a : α) :
        Subset x (f a) → Subset (f a) x → Mem x (sup f)
end

/-- Equivalencia extensional de Aczel (A ≡ B).
    Dos conjuntos son equivalentes si tienen los mismos elementos (A ⊆ B ∧ B ⊆ A). -/
def Equiv (x y : Tree) : Prop := Subset x y ∧ Subset y x

instance : Membership Tree Tree := ⟨fun y x => Mem x y⟩
instance : HasSubset Tree := ⟨Subset⟩

def Equiv.left {x y : Tree} (h : Equiv x y) : Subset x y := h.1
def Equiv.right {x y : Tree} (h : Equiv x y) : Subset y x := h.2

theorem Equiv.intro {x y : Tree} (h1 : Subset x y) (h2 : Subset y x) : Equiv x y := ⟨h1, h2⟩

theorem mem_sup_equiv {x : Tree} {α : Type u} {f : α → Tree} (a : α) (h : Equiv x (f a)) : Mem x (sup f) :=
  .mem_sup a h.left h.right

def Subset_refl (x : Tree) : Subset x x :=
  match x with
  | .sup f => .sup_subset fun a => .mem_sup a (Subset_refl (f a)) (Subset_refl (f a))

def trans_all (y : Tree) :
  (∀ {x z}, Subset x y → Subset y z → Subset x z) ∧
  (∀ {x z}, Mem x y → Subset y z → Mem x z) ∧
  (∀ {x z}, Subset y x → Subset x y → Mem y z → Mem x z) :=
  let mem_sub : ∀ {x z}, Mem x y → Subset y z → Mem x z := fun {_ z} h1 h2 =>
    match y, z, h2 with
    | _, _, @Subset.sup_subset _ g _ hsub2 =>
      match h1 with
      | @Mem.mem_sup _ _ _ a hx_fa hfa_x => (trans_all (g a)).2.2 hfa_x hx_fa (hsub2 a)

  let sub_sub : ∀ {x z}, Subset x y → Subset y z → Subset x z := fun {x _} h1 h2 =>
    match x, h1 with
    | _, @Subset.sup_subset _ f _ hsub => .sup_subset fun a => mem_sub (hsub a) h2

  let eq_mem : ∀ {x z}, Subset y x → Subset x y → Mem y z → Mem x z := fun {_ z} hyx hxy hyz =>
    match z, hyz with
    | _, @Mem.mem_sup _ _ g a hyg hgy =>
      .mem_sup a (sub_sub hxy hyg) (sub_sub hgy hyx)

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

end Tree

/-- Universo de Conjuntos como cociente extensional -/
abbrev USet := Quotient Tree.Setoid

namespace USet

theorem Subset_respects {x₁ x₂ y₁ y₂ : Tree} (hx : Tree.Equiv x₁ x₂) (hy : Tree.Equiv y₁ y₂) : Tree.Subset x₁ y₁ = Tree.Subset x₂ y₂ :=
  propext ⟨fun h => Tree.Subset_trans (Tree.Subset_trans hx.right h) hy.left,
           fun h => Tree.Subset_trans (Tree.Subset_trans hx.left h) hy.right⟩

theorem Mem_respects {x₁ x₂ y₁ y₂ : Tree} (hx : Tree.Equiv x₁ x₂) (hy : Tree.Equiv y₁ y₂) : Tree.Mem x₁ y₁ = Tree.Mem x₂ y₂ :=
  propext ⟨fun h => Tree.Mem_Subset_trans (Tree.Equiv_Mem_trans (Tree.Equiv_symm hx) h) hy.left,
           fun h => Tree.Mem_Subset_trans (Tree.Equiv_Mem_trans hx h) hy.right⟩

def Subset (a b : USet) : Prop :=
  Quotient.lift₂ Tree.Subset (fun _ _ _ _ hx hy => Subset_respects hx hy) a b

def Mem (a b : USet) : Prop :=
  Quotient.lift₂ Tree.Mem (fun _ _ _ _ hx hy => Mem_respects hx hy) a b

instance : HasSubset USet := ⟨Subset⟩
instance : Membership USet USet := ⟨fun y x => Mem x y⟩

theorem ext_iff (a b : USet) : a = b ↔ (a ⊆ b ∧ b ⊆ a) := by
  induction a using Quotient.ind
  induction b using Quotient.ind
  exact ⟨fun h => ⟨(Quotient.exact h).1, (Quotient.exact h).2⟩, fun h => Quotient.sound ⟨h.1, h.2⟩⟩

theorem ext {a b : USet} (h1 : a ⊆ b) (h2 : b ⊆ a) : a = b :=
  (ext_iff a b).mpr ⟨h1, h2⟩

end USet

end UnivSets
