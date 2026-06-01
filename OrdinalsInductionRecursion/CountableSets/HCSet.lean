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
    | sup_subset {f : ℕ₀ → Tree} {y : Tree} : (∀ n, Subset (f n) y) → Subset (.sup f) y

  /-- Relación de pertenencia (a ∈ B) al estilo Aczel.
      a ∈ B significa que `a` es equivalente a algún elemento que compone directamente a `B`. -/
  inductive Mem : Tree → Tree → Prop where
    | mem_succ {x y : Tree} : Equiv x y → Mem x (.succ y)
    | mem_sup {x : Tree} {f : ℕ₀ → Tree} (n : ℕ₀) : Equiv x (f n) → Mem x (.sup f)

  /-- Equivalencia extensional de Aczel (A ≡ B).
      Dos conjuntos son equivalentes si tienen los mismos elementos (A ⊆ B ∧ B ⊆ A). -/
  inductive Equiv : Tree → Tree → Prop where
    | intro {x y : Tree} : Subset x y → Subset y x → Equiv x y
end

instance : Membership Tree Tree := ⟨Mem⟩
instance : HasSubset Tree := ⟨Subset⟩

def Equiv.left {x y : Tree} (h : Equiv x y) : Subset x y :=
  match h with
  | .intro h1 _ => h1

def Equiv.right {x y : Tree} (h : Equiv x y) : Subset y x :=
  match h with
  | .intro _ h2 => h2

end CountableSets
