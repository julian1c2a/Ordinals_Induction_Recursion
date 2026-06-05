import OrdinalsInductionRecursion.DybjerSet.Tree

namespace DybjerSet

open Tree

-- ══════════════════════════════════════════════════════════════════
-- § 1. Conjunto Vacío
-- ══════════════════════════════════════════════════════════════════

def empty : DSet := Quotient.mk DybjerSet.Tree.Setoid .zero

theorem not_mem_empty (x : DSet) : ¬ (x ∈ empty) := by
  induction x using Quotient.ind
  rename_i a
  intro h
  have h' : DybjerSet.Tree.Mem a .zero := h
  cases h'

-- ══════════════════════════════════════════════════════════════════
-- § 2. Adjunción (Inserción de un elemento)
-- ══════════════════════════════════════════════════════════════════

open DybjerOrd

def insertTree (a b : Tree) : Tree :=
  match b with
  | .zero => .succ a
  | .succ c => .sup (.sum .unit .unit) fun x => match x with
    | Sum.inl _ => a
    | Sum.inr _ => c
  | .sup c f => .sup (.sum .unit c) fun x => match x with
    | Sum.inl _ => a
    | Sum.inr y => f y

-- Extensionalidad ya probada en DSet.ext

end DybjerSet
