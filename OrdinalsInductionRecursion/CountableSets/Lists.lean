import Peano
import Peano.PeanoNat.Pairing

namespace CountableSets

open Peano
open Peano.Pairing

/-- Representación de Conjuntos Hereditariamente Numerables mediante
    conjuntos de caminos (Listas de Naturales) cerrados por prefijos. (Opción B)
    Un camino `n::l` significa "toma el hijo n-ésimo, y luego sigue el camino l". -/
structure TreeList where
  paths : List ℕ₀ → Prop
  has_root : paths []
  prefix_closed : ∀ l n, paths (l ++ [n]) → paths l

namespace TreeList

/-- El conjunto vacío: el árbol que solo tiene la raíz, sin hijos. -/
def empty : TreeList where
  paths := fun l => l = []
  has_root := rfl
  prefix_closed := by
    intro l n h
    have h_nil := List.append_eq_nil_iff.mp h
    cases h_nil.right

/-- Subárbol en la rama n. Si n no es una rama válida, será el árbol vacío. -/
def child (t : TreeList) (n : ℕ₀) : TreeList where
  paths := fun l => t.paths (n :: l) ∨ l = []
  has_root := Or.inr rfl
  prefix_closed := by
    intro l m h
    cases h with
    | inl h1 =>
      have h1' : t.paths ((n :: l) ++ [m]) := h1
      exact Or.inl (t.prefix_closed (n :: l) m h1')
    | inr h2 =>
      have h_nil := List.append_eq_nil_iff.mp h2
      cases h_nil.right

/-- Unión de un árbol: recoge todos los hijos de los hijos (sub-subárboles).
    Mapeamos el sub-subárbol (n, m) a la rama k usando Cantor. -/
def union (t : TreeList) : TreeList where
  paths := fun l => l = [] ∨ 
    match l with
    | [] => True
    | k :: rest => 
      t.paths ((cantorUnpair k).fst :: (cantorUnpair k).snd :: rest)
  has_root := Or.inl rfl
  prefix_closed := by
    intro l c h
    cases h with
    | inl h1 =>
      have h_nil := List.append_eq_nil_iff.mp h1
      cases h_nil.right
    | inr h2 =>
      cases l with
      | nil => exact Or.inl rfl
      | cons k rest =>
        have h_paths : t.paths (((cantorUnpair k).fst :: (cantorUnpair k).snd :: rest) ++ [c]) := h2
        exact Or.inr (t.prefix_closed ((cantorUnpair k).fst :: (cantorUnpair k).snd :: rest) c h_paths)

/-- Inserción de un elemento: a ∪ {b}. -/
def insert (a b : TreeList) : TreeList where
  paths := fun l => l = [] ∨ 
    match l with
    | [] => True
    | Peano.ℕ₀.zero :: rest => b.paths rest
    | Peano.ℕ₀.succ n :: rest => a.paths (n :: rest)
  has_root := Or.inl rfl
  prefix_closed := by
    intro l c h
    cases h with
    | inl h1 =>
      have h_nil := List.append_eq_nil_iff.mp h1
      cases h_nil.right
    | inr h2 =>
      cases l with
      | nil => exact Or.inl rfl
      | cons k rest =>
        cases k with
        | zero =>
          have h_paths : b.paths (rest ++ [c]) := h2
          exact Or.inr (b.prefix_closed rest c h_paths)
        | succ n =>
          have h_paths : a.paths (n :: (rest ++ [c])) := h2
          have h_paths' : a.paths ((n :: rest) ++ [c]) := h_paths
          exact Or.inr (a.prefix_closed (n :: rest) c h_paths')

/-- Una relación R es una bisimulación si relaciona árboles con las mismas subestructuras -/
def IsBisimulation (R : TreeList → TreeList → Prop) : Prop :=
  ∀ a b, R a b → 
    (∀ n, a.paths [n] → ∃ m, b.paths [m] ∧ R (child a n) (child b m)) ∧
    (∀ m, b.paths [m] → ∃ n, a.paths [n] ∧ R (child a n) (child b m))

/-- Equivalencia extensional definida por la existencia de una bisimulación -/
def Equiv (x y : TreeList) : Prop :=
  ∃ R, IsBisimulation R ∧ R x y

/-- Subconjunto en árboles de listas: todo hijo válido de x es equivalente a un hijo válido de y -/
def Subset (x y : TreeList) : Prop :=
  ∀ n, x.paths [n] → ∃ m, y.paths [m] ∧ Equiv (child x n) (child y m)

/-- Pertenencia en árboles de listas: x es equivalente a algún hijo válido de y -/
def Mem (x y : TreeList) : Prop :=
  ∃ n, y.paths [n] ∧ Equiv x (child y n)

instance : Membership TreeList TreeList := ⟨fun y x => Mem x y⟩
instance : HasSubset TreeList := ⟨Subset⟩

-- ====================================================================
-- Propiedades Básicas y Axiomas
-- ====================================================================

theorem not_mem_empty (x : TreeList) : ¬ (x ∈ empty) := by
  intro h
  have h' : Mem x empty := h
  rcases h' with ⟨n, hn, _⟩
  have h_nil : [n] = [] := hn
  contradiction

/-- Dos árboles con los mismos caminos son extensionalmente equivalentes -/
theorem equiv_of_paths_eq (x y : TreeList) (h : ∀ l, x.paths l ↔ y.paths l) : Equiv x y := by
  let R := fun (a b : TreeList) => ∀ l, a.paths l ↔ b.paths l
  have hR : IsBisimulation R := by
    intro a b hab
    constructor
    · intro n hn
      have hbn : b.paths [n] := (hab [n]).mp hn
      have hR_child : R (child a n) (child b n) := fun l =>
        Iff.intro
          (fun h2 => match h2 with
            | Or.inl h3 => Or.inl ((hab (n :: l)).mp h3)
            | Or.inr h4 => Or.inr h4)
          (fun h2 => match h2 with
            | Or.inl h3 => Or.inl ((hab (n :: l)).mpr h3)
            | Or.inr h4 => Or.inr h4)
      exact ⟨n, hbn, hR_child⟩
    · intro m hm
      have ham : a.paths [m] := (hab [m]).mpr hm
      have hR_child : R (child a m) (child b m) := fun l =>
        Iff.intro
          (fun h2 => match h2 with
            | Or.inl h3 => Or.inl ((hab (m :: l)).mp h3)
            | Or.inr h4 => Or.inr h4)
          (fun h2 => match h2 with
            | Or.inl h3 => Or.inl ((hab (m :: l)).mpr h3)
            | Or.inr h4 => Or.inr h4)
      exact ⟨m, ham, hR_child⟩
  exact ⟨R, hR, h⟩

end TreeList

end CountableSets
