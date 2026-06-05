import OrdinalsInductionRecursion.TarskiSet.Tree

namespace TarskiSet

open Tree

-- ══════════════════════════════════════════════════════════════════
-- § 1. Conjunto Vacío
-- ══════════════════════════════════════════════════════════════════

def empty : TSet := Quotient.mk TarskiSet.Tree.Setoid .zero

theorem not_mem_empty (x : TSet) : ¬ (x ∈ empty) := by
  induction x using Quotient.ind
  rename_i a
  intro h
  have h' : TarskiSet.Tree.Mem a .zero := h
  cases h'

-- ══════════════════════════════════════════════════════════════════
-- § 2. Adjunción (Inserción de un elemento)
-- ══════════════════════════════════════════════════════════════════

open TarskiOrd

def insertTree (a b : Tree) : Tree :=
  match b with
  | .zero => .succ a
  | .succ c => .sup (.sum .unit .unit) fun x => match x with
    | Sum.inl _ => a
    | Sum.inr _ => c
  | .sup c f => .sup (.sum .unit c) fun x => match x with
    | Sum.inl _ => a
    | Sum.inr y => f y

-- Aquí podríamos probar extensionalidad de la inserción y levantarla al cociente,
-- pero el axioma de extensionalidad ya está en Tree.lean (TSet.ext).

end TarskiSet
