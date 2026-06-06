import OrdinalsInductionRecursion.DybjerOrd.Cardinals

namespace DybjerOrd
open DPreOrd
open Classical

-- ==========================================
-- Orden Cardinal (cardLe)
-- ==========================================

/-- El orden cardinal es simplemente la inyectabilidad. -/
def cardLe (x y : DOrdinal) : Prop := InjectsInto x y

/-- Reflexividad del orden cardinal -/
theorem cardLe_refl (x : DOrdinal) : cardLe x x :=
  Subset_implies_InjectsInto (Quotient.inductionOn x fun a => DSubset_refl a)

/-- Transitividad del orden cardinal -/
theorem cardLe_trans {x y z : DOrdinal} (h1 : cardLe x y) (h2 : cardLe y z) : cardLe x z :=
  InjectsInto_trans h1 h2

/-- El orden ordinal implica el orden cardinal -/
theorem ordinal_le_implies_card_le {x y : DOrdinal} (h : DOrdinal.Subset x y) : cardLe x y :=
  Subset_implies_InjectsInto h

/-- Orden estricto cardinal -/
def cardLt (x y : DOrdinal) : Prop := cardLe x y ∧ ¬ cardLe y x

-- ==========================================
-- Monotonía Cardinal
-- ==========================================

-- Las operaciones cardAdd y cardMul preservan el orden cardinal.
-- Dejamos declarada la intención de monotonía.

end DybjerOrd
